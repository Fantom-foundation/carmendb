#include "archive/leveldb/archive.h"

#include <filesystem>
#include <memory>
#include <span>
#include <type_traits>

#include "archive/leveldb/keys.h"
#include "backend/common/leveldb/leveldb.h"
#include "common/byte_util.h"
#include "common/status_util.h"

namespace carmen::archive::leveldb {

using ::carmen::backend::LDBEntry;
using ::carmen::backend::LevelDb;
using ::carmen::backend::LevelDbIterator;

namespace internal {

class Archive {
 public:
  static absl::StatusOr<std::unique_ptr<Archive>> Open(
      const std::filesystem::path directory) {
    ASSIGN_OR_RETURN(auto db, LevelDb::Open(directory));
    return std::unique_ptr<Archive>(new Archive(std::move(db)));
  }

  absl::Status Add(BlockId block, const Update& update) {
    // TODO: use a batch insert.

    for (const auto& [addr, balance] : update.GetBalances()) {
      RETURN_IF_ERROR(db_.Add({GetBalanceKey(addr, block), AsChars(balance)}));
    }

    for (const auto& [addr, code] : update.GetCodes()) {
      RETURN_IF_ERROR(db_.Add(
          {GetCodeKey(addr, block),
           std::span<const char>(reinterpret_cast<const char*>(code.Data()),
                                 code.Size())}));
    }

    for (const auto& [addr, nonce] : update.GetNonces()) {
      RETURN_IF_ERROR(db_.Add({GetNonceKey(addr, block), AsChars(nonce)}));
    }

    return absl::OkStatus();
    // return db_.AddBatch(entries);
  }

  template <typename Value>
  absl::StatusOr<Value> FindMostRecentFor(BlockId block, const Address& address,
                                          std::span<const char> key) {
    ASSIGN_OR_RETURN(auto iter, db_.GetLowerBound(key));
    if (iter.IsEnd()) {
      RETURN_IF_ERROR(iter.Prev());
    } else {
      if (iter.Key().size() != key.size() ||
          std::memcmp(iter.Key().data(), key.data(), key.size()) != 0) {
        RETURN_IF_ERROR(iter.Prev());
      }
    }
    if (!iter.Valid() || iter.Key().size() != key.size()) {
      return Value{};
    }

    ASSIGN_OR_RETURN(auto view, PropertyKeyView::Parse(iter.Key()));
    if (block < view.GetBlockId() || address != view.GetAddress()) {
      return Value{};
    }

    if (!std::is_same_v<Value, Code> && iter.Value().size() != sizeof(Value)) {
      return absl::InternalError("stored value has wrong format");
    }
    Value result;
    result.SetBytes(std::as_bytes(iter.Value()));
    return result;
  }

  absl::StatusOr<Balance> GetBalance(BlockId block, const Address& address) {
    return FindMostRecentFor<Balance>(block, address,
                                      GetBalanceKey(address, block));
  }

  absl::StatusOr<Code> GetCode(BlockId block, const Address& address) {
    return FindMostRecentFor<Code>(block, address, GetCodeKey(address, block));
  }

  absl::StatusOr<Nonce> GetNonce(BlockId block, const Address& address) {
    return FindMostRecentFor<Nonce>(block, address,
                                    GetNonceKey(address, block));
  }

  absl::Status Flush() { return db_.Flush(); }

  absl::Status Close() { return db_.Close(); }

 private:
  Archive(LevelDb db) : db_(std::move(db)) {}
  LevelDb db_;
};

}  // namespace internal

LevelDbArchive::LevelDbArchive(LevelDbArchive&&) = default;

LevelDbArchive::LevelDbArchive(std::unique_ptr<internal::Archive> archive)
    : impl_(std::move(archive)){};

LevelDbArchive& LevelDbArchive::operator=(LevelDbArchive&&) = default;

LevelDbArchive::~LevelDbArchive() { Close().IgnoreError(); };

absl::StatusOr<LevelDbArchive> LevelDbArchive::Open(
    std::filesystem::path directory) {
  // TODO: create directory if it does not exist.
  auto path = directory;
  if (std::filesystem::is_directory(directory)) {
    path = path / "archive.sqlite";
  }
  ASSIGN_OR_RETURN(auto impl, internal::Archive::Open(path));
  return LevelDbArchive(std::move(impl));
}

absl::Status LevelDbArchive::Add(BlockId block, const Update& update) {
  RETURN_IF_ERROR(CheckState());
  return impl_->Add(block, update);
}

absl::StatusOr<Balance> LevelDbArchive::GetBalance(BlockId block,
                                                   const Address& account) {
  RETURN_IF_ERROR(CheckState());
  return impl_->GetBalance(block, account);
}

absl::StatusOr<Code> LevelDbArchive::GetCode(BlockId block,
                                             const Address& account) {
  RETURN_IF_ERROR(CheckState());
  return impl_->GetCode(block, account);
}

absl::StatusOr<Nonce> LevelDbArchive::GetNonce(BlockId block,
                                               const Address& account) {
  RETURN_IF_ERROR(CheckState());
  return impl_->GetNonce(block, account);
}

absl::Status LevelDbArchive::Flush() {
  if (!impl_) return absl::OkStatus();
  return impl_->Flush();
}

absl::Status LevelDbArchive::Close() {
  if (!impl_) return absl::OkStatus();
  auto result = impl_->Close();
  impl_ = nullptr;
  return result;
}

absl::Status LevelDbArchive::CheckState() const {
  if (impl_) return absl::OkStatus();
  return absl::FailedPreconditionError("Archive not connected to DB.");
}

}  // namespace carmen::archive::leveldb
