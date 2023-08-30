package mpt

//go:generate mockgen -source hasher.go -destination hasher_mocks.go -package mpt

import (
	"crypto/sha256"
	"errors"
	"fmt"
	"reflect"
	"sync"

	"golang.org/x/crypto/sha3"

	"github.com/Fantom-foundation/Carmen/go/common"
	"github.com/Fantom-foundation/Carmen/go/state/mpt/rlp"
)

// Hasher is an interface for implementations of MPT node hashing algorithms. It is
// intended to be one of the differentiator between S4 and derived schemas.
type Hasher interface {
	// GetHash requests a hash value for the given node. To compute the node's hash,
	// implementations may recursively resolve hashes for other nodes using the given
	// HashSource implementation. Due to its recursive nature, multiple calls to the
	// function may be nested and/or processed concurrently. Thus, implementations are
	// required to be reentrant and thread-safe.
	GetHash(Node, NodeSource, HashSource) (common.Hash, error)
}

type HashSource interface {
	getHashFor(NodeId) (common.Hash, error)
}

// DirectHasher implements a simple, direct node-value hashing algorithm that combines
// the content of individual nodes with the hashes of referenced child nodes into a
// hash for individual nodes.
type DirectHasher struct{}

// GetHash implements the DirectHasher's hashing algorithm.
func (h DirectHasher) GetHash(node Node, _ NodeSource, source HashSource) (common.Hash, error) {
	hash := common.Hash{}
	if _, ok := node.(EmptyNode); ok {
		return hash, nil
	}
	hasher := sha256.New()
	switch node := node.(type) {
	case *AccountNode:
		hasher.Write([]byte{'A'})
		hasher.Write(node.address[:])
		hasher.Write(node.info.Balance[:])
		hasher.Write(node.info.Nonce[:])
		hasher.Write(node.info.CodeHash[:])
		if hash, err := source.getHashFor(node.storage); err == nil {
			hasher.Write(hash[:])
		} else {
			return hash, err
		}

	case *BranchNode:
		hasher.Write([]byte{'B'})
		// TODO: compute sub-tree hashes in parallel
		var wg sync.WaitGroup
		wg.Add(16)
		var errs [16]error
		var hashes [16]common.Hash
		for i, child := range node.children {
			go func(i int, child NodeId) {
				defer wg.Done()
				if hash, err := source.getHashFor(child); err == nil {
					hashes[i] = hash
				} else {
					errs[i] = err
				}
			}(i, child)
		}
		wg.Wait()
		if err := errors.Join(errs[:]...); err != nil {
			return hash, nil
		}
		for _, hash := range hashes {
			hasher.Write(hash[:])
		}
		hasher.Write(hash[:])

	case *ExtensionNode:
		hasher.Write([]byte{'E'})
		hasher.Write(node.path.path[:])
		if hash, err := source.getHashFor(node.next); err == nil {
			hasher.Write(hash[:])
		} else {
			return hash, err
		}

	case *ValueNode:
		hasher.Write([]byte{'V'})
		hasher.Write(node.key[:])
		hasher.Write(node.value[:])

	default:
		return hash, fmt.Errorf("unsupported node type: %v", reflect.TypeOf(node))
	}
	hasher.Sum(hash[0:0])
	return hash, nil
}

// Based on Appendix D of https://ethereum.github.io/yellowpaper/paper.pdf
type MptHasher struct{}

// GetHash implements the MPT hashing algorithm.
func (h MptHasher) GetHash(node Node, nodes NodeSource, hashes HashSource) (common.Hash, error) {
	data, err := encode(node, nodes, hashes)
	if err != nil {
		return common.Hash{}, err
	}
	return keccak256(data), nil
}

func keccak256(data []byte) common.Hash {
	return common.GetHash(sha3.NewLegacyKeccak256(), data)
}

func encode(node Node, nodes NodeSource, hashes HashSource) ([]byte, error) {
	switch trg := node.(type) {
	case EmptyNode:
		return encodeEmpty(trg, nodes, hashes)
	case *AccountNode:
		return encodeAccount(trg, nodes, hashes)
	case *BranchNode:
		return encodeBranch(trg, nodes, hashes)
	case *ExtensionNode:
		return encodeExtension(trg, nodes, hashes)
	case *ValueNode:
		return encodeValue(trg, nodes, hashes)
	default:
		return nil, fmt.Errorf("unsupported node type: %v", reflect.TypeOf(node))
	}
}

// getLowerBoundForEncodedSize computes a lower bound for the length of the RLP encoding of
// the given node. The provided limit indicates an upper bound beyond which any higher
// result is no longer relevant.
func getLowerBoundForEncodedSize(node Node, limit int, nodes NodeSource) (int, error) {
	switch trg := node.(type) {
	case EmptyNode:
		return getLowerBoundForEncodedSizeEmpty(trg, limit, nodes)
	case *AccountNode:
		return getLowerBoundForEncodedSizeAccount(trg, limit, nodes)
	case *BranchNode:
		return getLowerBoundForEncodedSizeBranch(trg, limit, nodes)
	case *ExtensionNode:
		return getLowerBoundForEncodedSizeExtension(trg, limit, nodes)
	case *ValueNode:
		return getLowerBoundForEncodedSizeValue(trg, limit, nodes)
	default:
		return 0, fmt.Errorf("unsupported node type: %v", reflect.TypeOf(node))
	}
}

var emptyStringRlpEncoded = rlp.Encode(rlp.String{})

func encodeEmpty(EmptyNode, NodeSource, HashSource) ([]byte, error) {
	return emptyStringRlpEncoded, nil
}

func getLowerBoundForEncodedSizeEmpty(node EmptyNode, limit int, nodes NodeSource) (int, error) {
	return len(emptyStringRlpEncoded), nil
}

func encodeBranch(node *BranchNode, nodes NodeSource, hashes HashSource) ([]byte, error) {
	children := node.children
	items := make([]rlp.Item, len(children)+1)

	var wg sync.WaitGroup
	var errs [16]error
	for i, child := range children {
		if child.IsEmpty() {
			items[i] = rlp.String{}
			continue
		}

		wg.Add(1)
		go func(i int, child NodeId) {
			defer wg.Done()
			node, err := nodes.getNode(child)
			if err != nil {
				errs[i] = err
				return
			}
			defer node.Release()

			minSize, err := getLowerBoundForEncodedSize(node.Get(), 32, nodes)
			if err != nil {
				errs[i] = err
				return
			}

			var encoded []byte
			if minSize < 32 {
				encoded, err = encode(node.Get(), nodes, hashes)
				if err != nil {
					errs[i] = err
					return
				}
				if len(encoded) >= 32 {
					encoded = nil
				}
			}

			if encoded == nil {
				hash, err := hashes.getHashFor(child)
				if err != nil {
					errs[i] = err
					return
				}
				items[i] = rlp.String{Str: hash[:]}
			} else {
				items[i] = rlp.Encoded{Data: encoded}
			}
		}(i, child)
	}

	// There is one 17th entry which would be filled if this node is a terminator. However,
	// branch nodes are never terminators in State or Storage Tries.
	items[len(children)] = &rlp.String{}

	wg.Wait()

	if err := errors.Join(errs[:]...); err != nil {
		return nil, err
	}

	return rlp.Encode(rlp.List{Items: items}), nil
}

func getLowerBoundForEncodedSizeBranch(node *BranchNode, limit int, nodes NodeSource) (int, error) {
	var emptySize = len(emptyStringRlpEncoded)
	sum := emptySize // the 17th element.
	for _, child := range node.children {
		if sum >= limit {
			return limit, nil
		}
		if child.IsEmpty() {
			sum += emptySize
			continue
		}

		node, err := nodes.getNode(child)
		if err != nil {
			return 0, err
		}
		defer node.Release()

		size, err := getLowerBoundForEncodedSize(node.Get(), limit-sum, nodes)
		if err != nil {
			return 0, err
		}
		if size >= 32 {
			size = 32
		}
		sum += size
	}
	return sum + 1, nil // the list length adds another byte
}

func encodeExtension(node *ExtensionNode, nodes NodeSource, hashes HashSource) ([]byte, error) {
	items := make([]rlp.Item, 2)

	numNibbles := node.path.Length()
	packedNibbles := node.path.GetPackedNibbles()
	items[0] = &rlp.String{Str: encodePartialPath(packedNibbles, numNibbles, false)}

	next, err := nodes.getNode(node.next)
	if err != nil {
		return nil, err
	}
	defer next.Release()

	minSize, err := getLowerBoundForEncodedSize(next.Get(), 32, nodes)
	if err != nil {
		return nil, err
	}

	var encoded []byte
	if minSize < 32 {
		encoded, err = encode(next.Get(), nodes, hashes)
		if err != nil {
			return nil, err
		}
		if len(encoded) >= 32 {
			encoded = nil
		}
	}

	if encoded == nil {
		hash, err := hashes.getHashFor(node.next)
		if err != nil {
			return nil, err
		}
		items[1] = rlp.String{Str: hash[:]}
	} else {
		// TODO: the use of a direct encoding here is done for
		// symetry with the branch node, but there is no unit test
		// for this yet; it would require to find two keys or address
		// with a very long common hash prefix.
		items[1] = rlp.Encoded{Data: encoded}
	}

	return rlp.Encode(rlp.List{Items: items}), nil
}

func getLowerBoundForEncodedSizeExtension(node *ExtensionNode, limit int, nodes NodeSource) (int, error) {
	sum := 1 // list header

	sum += getEncodedPartialPathSize(node.path.Length())
	if sum >= limit {
		return sum, nil
	}

	next, err := nodes.getNode(node.next)
	if err != nil {
		return 0, err
	}
	defer next.Release()

	size, err := getLowerBoundForEncodedSize(next.Get(), limit-sum, nodes)
	if err != nil {
		return 0, err
	}
	if size > 32 {
		size = 32
	}
	sum += size

	return sum, nil
}

func encodeAccount(node *AccountNode, nodes NodeSource, hashes HashSource) ([]byte, error) {
	storageRoot := node.storage
	storageHash, err := hashes.getHashFor(storageRoot)
	if err != nil {
		return nil, err
	}

	// Encode the account information to get the value.
	info := node.info
	items := make([]rlp.Item, 4)
	items[0] = &rlp.Uint64{Value: info.Nonce.ToUint64()}
	items[1] = &rlp.BigInt{Value: info.Balance.ToBigInt()}
	items[2] = &rlp.String{Str: storageHash[:]}
	items[3] = &rlp.String{Str: info.CodeHash[:]}
	value := rlp.Encode(rlp.List{Items: items})

	// Encode the leaf node by combining the partial path with the value.
	items = items[0:2]
	items[0] = &rlp.String{Str: encodeAddressPath(node.address, int(node.pathLength), nodes)}
	items[1] = &rlp.String{Str: value}
	return rlp.Encode(rlp.List{Items: items}), nil
}

func getLowerBoundForEncodedSizeAccount(node *AccountNode, limit int, nodes NodeSource) (int, error) {
	size := 32 + 32 // storage and code hash
	// There is no need for anything more accurate so far, since
	// all queries will use a limit <= 32.
	return size, nil
}

func encodeValue(node *ValueNode, nodes NodeSource, hashSource HashSource) ([]byte, error) {
	items := make([]rlp.Item, 2)

	// The first item is an encoded path fragment.
	items[0] = &rlp.String{Str: encodeKeyPath(node.key, int(node.pathLength), nodes)}

	// The second item is the value without leading zeros.
	value := node.value[:]
	for len(value) > 0 && value[0] == 0 {
		value = value[1:]
	}
	items[1] = &rlp.String{Str: rlp.Encode(&rlp.String{Str: value[:]})}

	return rlp.Encode(rlp.List{Items: items}), nil
}

func getLowerBoundForEncodedSizeValue(node *ValueNode, limit int, nodes NodeSource) (int, error) {
	size := getEncodedPartialPathSize(int(node.pathLength))
	if size > 1 {
		size++ // one extra byte for the length
	}
	if size >= limit {
		return size, nil
	}

	value := node.value[:]
	for len(value) > 0 && value[0] == 0 {
		value = value[1:]
	}
	return size + len(value) + 1, nil
}

func encodeKeyPath(key common.Key, numNibbles int, nodes NodeSource) []byte {
	path := nodes.hashKey(key)
	return encodePartialPath(path[32-(numNibbles/2+numNibbles%2):], numNibbles, true)
}

func encodeAddressPath(address common.Address, numNibbles int, nodes NodeSource) []byte {
	path := nodes.hashAddress(address)
	return encodePartialPath(path[32-(numNibbles/2+numNibbles%2):], numNibbles, true)
}

// Requires packedNibbles to include nibbles as [0a bc de] or [ab cd ef]
func encodePartialPath(packedNibbles []byte, numNibbles int, targetsValue bool) []byte {
	// Path encosing derived from Ethereum.
	// see https://github.com/ethereum/go-ethereum/blob/v1.12.0/trie/encoding.go#L37
	oddLength := numNibbles%2 == 1
	compact := make([]byte, getEncodedPartialPathSize(numNibbles))

	// The high nibble of the first byte encodes the 'is-value' mark
	// and whether the length is even or odd.
	if targetsValue {
		compact[0] |= 1 << 5
	}
	compact[0] |= (byte(numNibbles) % 2) << 4 // odd flag

	// If there is an odd number of nibbles, the first is included in the
	// low-part of the compact path encoding.
	if oddLength {
		compact[0] |= packedNibbles[0] & 0xf
		packedNibbles = packedNibbles[1:]
	}
	// The rest of the nibbles can be copied.
	copy(compact[1:], packedNibbles)
	return compact
}

func getEncodedPartialPathSize(numNibbles int) int {
	return numNibbles/2 + 1
}
