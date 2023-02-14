package common

import (
	"bytes"
	"encoding/binary"
	"fmt"
	"sort"
)

// Update summarizes the effective changes to the state DB at the end of a block.
// It combines changes to the account state (created or deleted), balances, nonces
// codes, and slot updates.
//
// An example use of an update would look like this:
//
//	// Create an update.
//	update := Update{}
//	// Fill in changes.
//	// Note: for each type of change, updates must be in order and unique.
//	update.AppendCreateAccount(..)
//	update.AppendCreateAccount(..)
//	...
//	// Optionally, check that the provided data is valid (sorted and unique).
//	err := update.Check()
//
// Valid instances can then be forwarded to the State as a block update.
type Update struct {
	DeletedAccounts []Address
	CreatedAccounts []Address
	Balances        []BalanceUpdate
	Nonces          []NonceUpdate
	Codes           []CodeUpdate
	Slots           []SlotUpdate
}

// IsEmpty is true if there is no change covered by this update.
func (u *Update) IsEmpty() bool {
	return len(u.DeletedAccounts) == 0 &&
		len(u.CreatedAccounts) == 0 &&
		len(u.Balances) == 0 &&
		len(u.Nonces) == 0 &&
		len(u.Codes) == 0 &&
		len(u.Slots) == 0
}

// AppendDeleteAccount registers an account to be deleted in this block. Delete
// operations are the first to be carried out, leading to a clearing of the
// account's storage. Subsequent account creations or balance / nonce / slot
// updates will take effect after the deletion of the account.
func (u *Update) AppendDeleteAccount(addr Address) {
	u.AppendDeleteAccounts([]Address{addr})
}

// AppendDeleteAccounts is the same as AppendDeleteAccount, but for a slice.
func (u *Update) AppendDeleteAccounts(addr []Address) {
	u.DeletedAccounts = append(u.DeletedAccounts, addr...)
}

// AppendCreateAccount registers a new account to be created in this block.
// This takes affect after deleting the accounts listed in this update.
func (u *Update) AppendCreateAccount(addr Address) {
	u.AppendCreateAccounts([]Address{addr})
}

// AppendCreateAccounts is the same as AppendCreateAccount, but for a slice.
func (u *Update) AppendCreateAccounts(addr []Address) {
	u.CreatedAccounts = append(u.CreatedAccounts, addr...)
}

// AppendBalanceUpdate registers a balance update to be conducted.
func (u *Update) AppendBalanceUpdate(addr Address, balance Balance) {
	u.Balances = append(u.Balances, BalanceUpdate{addr, balance})
}

// AppendNonceUpdate registers a nonce update to be conducted.
func (u *Update) AppendNonceUpdate(addr Address, nonce Nonce) {
	u.Nonces = append(u.Nonces, NonceUpdate{addr, nonce})
}

// AppendCodeUpdate registers a code update to be conducted.
func (u *Update) AppendCodeUpdate(addr Address, code []byte) {
	u.Codes = append(u.Codes, CodeUpdate{addr, code})
}

// AppendSlotUpdate registers a slot value update to be conducted
func (u *Update) AppendSlotUpdate(addr Address, key Key, value Value) {
	u.Slots = append(u.Slots, SlotUpdate{addr, key, value})
}

// Normalize sorts all updates and removes duplicates.
func (u *Update) Normalize() error {
	var err error
	u.DeletedAccounts, err = sortAndMakeUnique(u.DeletedAccounts, accountLess, accountEqual)
	if err != nil {
		return err
	}
	u.CreatedAccounts, err = sortAndMakeUnique(u.CreatedAccounts, accountLess, accountEqual)
	if err != nil {
		return err
	}
	u.Balances, err = sortAndMakeUnique(u.Balances, balanceLess, balanceEqual)
	if err != nil {
		return err
	}
	u.Codes, err = sortAndMakeUnique(u.Codes, codeLess, codeEqual)
	if err != nil {
		return err
	}
	u.Nonces, err = sortAndMakeUnique(u.Nonces, nonceLess, nonceEqual)
	if err != nil {
		return err
	}
	u.Slots, err = sortAndMakeUnique(u.Slots, slotLess, slotEqual)
	if err != nil {
		return err
	}
	return nil
}

const updateEncodingVersion byte = 0

func UpdateFromBytes(data []byte) (Update, error) {
	if len(data) < 1+6*4 {
		return Update{}, fmt.Errorf("invalid encoding, too few bytes")
	}
	if data[0] != updateEncodingVersion {
		return Update{}, fmt.Errorf("unknown encoding version: %d", data[0])
	}

	data = data[1:]
	deletedAccountSize := readUint32(data[0:])
	createdAccountSize := readUint32(data[4:])
	balancesSize := readUint32(data[8:])
	codesSize := readUint32(data[12:])
	noncesSize := readUint32(data[16:])
	slotsSize := readUint32(data[20:])

	data = data[24:]

	res := Update{}

	// Read list of deleted accounts
	if deletedAccountSize > 0 {
		if len(data) < int(deletedAccountSize)*len(Address{}) {
			return res, fmt.Errorf("invalid encoding, truncated address list")
		}
		res.DeletedAccounts = make([]Address, deletedAccountSize)
		for i := 0; i < int(deletedAccountSize); i++ {
			copy(res.DeletedAccounts[i][:], data[:])
			data = data[len(Address{}):]
		}
	}

	// Read list of created accounts
	if createdAccountSize > 0 {
		if len(data) < int(createdAccountSize)*len(Address{}) {
			return res, fmt.Errorf("invalid encoding, truncated address list")
		}
		res.CreatedAccounts = make([]Address, createdAccountSize)
		for i := 0; i < int(createdAccountSize); i++ {
			copy(res.CreatedAccounts[i][:], data[:])
			data = data[len(Address{}):]
		}
	}

	// Read list of balance updates
	if balancesSize > 0 {
		if len(data) < int(balancesSize)*(len(Address{})+len(Balance{})) {
			return res, fmt.Errorf("invalid encoding, balance list truncated")
		}
		res.Balances = make([]BalanceUpdate, balancesSize)
		for i := 0; i < int(balancesSize); i++ {
			copy(res.Balances[i].Account[:], data[:])
			data = data[len(Address{}):]
			copy(res.Balances[i].Balance[:], data[:])
			data = data[len(Balance{}):]
		}
	}

	// Read list of code updates
	if codesSize > 0 {
		res.Codes = make([]CodeUpdate, codesSize)
		for i := 0; i < int(codesSize); i++ {
			if len(data) < len(Address{})+2 {
				return res, fmt.Errorf("invalid encoding, truncated code list")
			}
			copy(res.Codes[i].Account[:], data[:])
			data = data[len(Address{}):]
			codeLength := readUint16(data)
			data = data[2:]
			if len(data) < int(codeLength) {
				return res, fmt.Errorf("invalid encoding, truncated code")
			}
			res.Codes[i].Code = make([]byte, codeLength)
			copy(res.Codes[i].Code[:], data[0:codeLength])
			data = data[codeLength:]
		}
	}

	// Read list of nonce updates
	if noncesSize > 0 {
		if len(data) < int(noncesSize)*(len(Address{})+len(Nonce{})) {
			return res, fmt.Errorf("invalid encoding, nonce list truncated")
		}
		res.Nonces = make([]NonceUpdate, noncesSize)
		for i := 0; i < int(noncesSize); i++ {
			copy(res.Nonces[i].Account[:], data[:])
			data = data[len(Address{}):]
			copy(res.Nonces[i].Nonce[:], data[:])
			data = data[len(Nonce{}):]
		}
	}

	// Read list of slot updates
	if slotsSize > 0 {
		if len(data) < int(slotsSize)*(len(Address{})+len(Key{})+len(Value{})) {
			return res, fmt.Errorf("invalid encoding, slot list truncated")
		}
		res.Slots = make([]SlotUpdate, slotsSize)
		for i := 0; i < int(slotsSize); i++ {
			copy(res.Slots[i].Account[:], data[:])
			data = data[len(Address{}):]
			copy(res.Slots[i].Key[:], data[:])
			data = data[len(Key{}):]
			copy(res.Slots[i].Value[:], data[:])
			data = data[len(Value{}):]
		}
	}

	return res, nil
}

func (u *Update) ToBytes() []byte {
	const addrLength = len(Address{})
	size := 1 + 6*4 // version + sizes
	size += len(u.DeletedAccounts) * addrLength
	size += len(u.CreatedAccounts) * addrLength
	size += len(u.Balances) * (addrLength + len(Balance{}))
	size += len(u.Nonces) * (addrLength + len(Nonce{}))
	size += len(u.Slots) * (addrLength + len(Key{}) + len(Value{}))
	for _, cur := range u.Codes {
		size += addrLength + 2 + len(cur.Code)
	}

	res := make([]byte, 0, size)

	res = append(res, updateEncodingVersion)
	res = appendUint32(res, uint32(len(u.DeletedAccounts)))
	res = appendUint32(res, uint32(len(u.CreatedAccounts)))
	res = appendUint32(res, uint32(len(u.Balances)))
	res = appendUint32(res, uint32(len(u.Codes)))
	res = appendUint32(res, uint32(len(u.Nonces)))
	res = appendUint32(res, uint32(len(u.Slots)))

	for _, addr := range u.DeletedAccounts {
		res = append(res, addr[:]...)
	}
	for _, addr := range u.CreatedAccounts {
		res = append(res, addr[:]...)
	}
	for _, cur := range u.Balances {
		res = append(res, cur.Account[:]...)
		res = append(res, cur.Balance[:]...)
	}
	for _, cur := range u.Codes {
		res = append(res, cur.Account[:]...)
		res = appendUint16(res, uint16(len(cur.Code)))
		res = append(res, cur.Code...)
	}
	for _, cur := range u.Nonces {
		res = append(res, cur.Account[:]...)
		res = append(res, cur.Nonce[:]...)
	}
	for _, cur := range u.Slots {
		res = append(res, cur.Account[:]...)
		res = append(res, cur.Key[:]...)
		res = append(res, cur.Value[:]...)
	}

	return res
}

func readUint16(data []byte) uint16 {
	return binary.BigEndian.Uint16(data)
}

func readUint32(data []byte) uint32 {
	return binary.BigEndian.Uint32(data)
}

func appendUint16(data []byte, value uint16) []byte {
	return binary.BigEndian.AppendUint16(data, value)
}

func appendUint32(data []byte, value uint32) []byte {
	return binary.BigEndian.AppendUint32(data, value)
}

// Check verifies that all updates are unique and in order.
func (u *Update) Check() error {
	if !isSortedAndUnique(u.CreatedAccounts, accountLess) {
		return fmt.Errorf("created accounts are not in order or unique")
	}
	if !isSortedAndUnique(u.DeletedAccounts, accountLess) {
		return fmt.Errorf("deleted accounts are not in order or unique")
	}

	if !isSortedAndUnique(u.Balances, balanceLess) {
		return fmt.Errorf("balance updates are not in order or unique")
	}

	if !isSortedAndUnique(u.Nonces, nonceLess) {
		return fmt.Errorf("nonce updates are not in order or unique")
	}

	if !isSortedAndUnique(u.Codes, codeLess) {
		return fmt.Errorf("nonce updates are not in order or unique")
	}

	if !isSortedAndUnique(u.Slots, slotLess) {
		return fmt.Errorf("storage updates are not in order or unique")
	}

	// Make sure that there is no account created and deleted.
	for i, j := 0, 0; i < len(u.CreatedAccounts) && j < len(u.DeletedAccounts); {
		cmp := u.CreatedAccounts[i].Compare(&u.DeletedAccounts[j])
		if cmp == 0 {
			return fmt.Errorf("unable to create and delete same address in update: %v", u.CreatedAccounts[i])
		}
		if cmp < 0 {
			i++
		} else {
			j++
		}
	}

	return nil
}

func accountLess(a, b *Address) bool {
	return a.Compare(b) < 0
}

func accountEqual(a, b *Address) bool {
	return *a == *b
}

func balanceLess(a, b *BalanceUpdate) bool {
	return accountLess(&a.Account, &b.Account)
}

func balanceEqual(a, b *BalanceUpdate) bool {
	return *a == *b
}

func nonceLess(a, b *NonceUpdate) bool {
	return accountLess(&a.Account, &b.Account)
}

func nonceEqual(a, b *NonceUpdate) bool {
	return *a == *b
}

func codeLess(a, b *CodeUpdate) bool {
	return accountLess(&a.Account, &b.Account)
}

func codeEqual(a, b *CodeUpdate) bool {
	return a.Account == b.Account && bytes.Equal(a.Code, b.Code)
}

func slotLess(a, b *SlotUpdate) bool {
	accountCompare := a.Account.Compare(&b.Account)
	return accountCompare < 0 || (accountCompare == 0 && a.Key.Compare(&b.Key) < 0)
}

func slotEqual(a, b *SlotUpdate) bool {
	return *a == *b
}

func (*Update) GetHash() Hash {
	return Hash{} // TODO
}

type BalanceUpdate struct {
	Account Address
	Balance Balance
}

type NonceUpdate struct {
	Account Address
	Nonce   Nonce
}

type CodeUpdate struct {
	Account Address
	Code    []byte
}

type SlotUpdate struct {
	Account Address
	Key     Key
	Value   Value
}

func sortAndMakeUnique[T any](list []T, less func(a, b *T) bool, equal func(a, b *T) bool) ([]T, error) {
	if len(list) <= 1 {
		return list, nil
	}
	sort.Slice(list, func(i, j int) bool { return less(&list[i], &list[j]) })
	res := make([]T, 0, len(list))
	res = append(res, list[0])
	for i := 1; i < len(list); i++ {
		end := &res[len(res)-1]
		if less(end, &list[i]) {
			res = append(res, list[i])
		} else if equal(end, &list[i]) {
			// skip duplicates
		} else {
			// Same key, but different values => this needs to fail
			return nil, fmt.Errorf("Unable to resolve duplicate element: %v and %v", *end, list[i])
		}
	}
	return res, nil
}

func isSortedAndUnique[T any](list []T, less func(a, b *T) bool) bool {
	for i := 0; i < len(list)-1; i++ {
		if !less(&list[i], &list[i+1]) {
			return false
		}
	}
	return true
}
