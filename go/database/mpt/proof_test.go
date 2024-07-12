// Copyright (c) 2024 Fantom Foundation
//
// Use of this software is governed by the Business Source License included
// in the LICENSE file and at fantom.foundation/bsl11.
//
// Change Date: 2028-4-16
//
// On the date above, in accordance with the Business Source License, use of
// this software will be governed by the GNU Lesser General Public License v3.

package mpt

import (
	"encoding/hex"
	"errors"
	"fmt"
	"github.com/Fantom-foundation/Carmen/go/common"
	"github.com/Fantom-foundation/Carmen/go/database/mpt/rlp"
	"github.com/Fantom-foundation/Carmen/go/database/mpt/shared"
	"go.uber.org/mock/gomock"
	"golang.org/x/exp/maps"
	"reflect"
	"testing"
)

func TestCreateWitnessProof_CanCreateProof(t *testing.T) {
	ctrl := gomock.NewController(t)

	address := common.Address{1}
	key := common.Key{2}

	ctxt := newNodeContextWithConfig(t, ctrl, S5LiveConfig)
	addressNibbles := AddressToNibblePath(address, ctxt)
	keyNibbles := KeyToNibblePath(key, ctxt)

	tests := map[string]struct {
		desc  NodeDesc
		value common.Value
	}{
		"account correct storage": {
			desc: &Branch{
				children: Children{
					addressNibbles[0]: &Branch{
						children: Children{
							addressNibbles[1]: &Extension{
								path: addressNibbles[2:50],
								next: &Account{address: address, pathLength: 14, info: AccountInfo{common.Nonce{1}, common.Balance{1}, common.Hash{0xAA}},
									storage: &Branch{
										children: Children{
											keyNibbles[0]: &Extension{path: keyNibbles[1:40], next: &Value{key: key, length: 24, value: common.Value{0x12}}},
										}}}},
						}}},
			},
			value: common.Value{0x12},
		},
		"account different storage": {
			desc: &Branch{
				children: Children{
					addressNibbles[0]: &Branch{
						children: Children{
							addressNibbles[1]: &Extension{
								path: addressNibbles[2:50],
								next: &Account{address: address, pathLength: 14, info: AccountInfo{common.Nonce{1}, common.Balance{1}, common.Hash{0xAA}},
									storage: &Branch{
										children: Children{
											keyNibbles[0]: &Extension{path: keyNibbles[1:40], next: &Value{key: common.Key{}, length: 24, value: common.Value{0x12}}},
										}}}},
						}}},
			},
			value: common.Value{},
		},
		"account storage path does not exist": {
			desc: &Branch{
				children: Children{
					addressNibbles[0]: &Branch{
						children: Children{
							addressNibbles[1]: &Extension{
								path: addressNibbles[2:50],
								next: &Account{address: address, pathLength: 14, info: AccountInfo{common.Nonce{1}, common.Balance{1}, common.Hash{0xAA}},
									storage: &Extension{path: keyNibbles[1:40], next: &Empty{}},
								}}}}},
			},
			value: common.Value{},
		},
		"storage empty value": {
			desc: &Branch{
				children: Children{
					addressNibbles[0]: &Branch{
						children: Children{
							addressNibbles[1]: &Extension{
								path: addressNibbles[2:50],
								next: &Account{address: address, pathLength: 14, info: AccountInfo{common.Nonce{1}, common.Balance{1}, common.Hash{0xAA}},
									storage: &Branch{
										children: Children{
											keyNibbles[0]: &Extension{path: keyNibbles[1:40], next: &Empty{}},
										}}}},
						}}},
			},
			value: common.Value{},
		},
		"account empty storage": {
			desc: &Branch{
				children: Children{
					addressNibbles[0]: &Branch{
						children: Children{
							addressNibbles[1]: &Extension{
								path: addressNibbles[2:50],
								next: &Account{address: address, pathLength: 14, info: AccountInfo{common.Nonce{1}, common.Balance{1}, common.Hash{0xAA}},
									storage: &Empty{}}},
						}}},
			},
			value: common.Value{},
		},
		"account path does not exist": {
			desc: &Branch{
				children: Children{
					addressNibbles[0]: &Branch{
						children: Children{
							addressNibbles[1]: &Extension{
								path: addressNibbles[2:50],
								next: Empty{},
							}}}},
			},
			value: common.Value{},
		},
		"different account": {
			desc: &Branch{
				children: Children{
					addressNibbles[0]: &Branch{
						children: Children{
							addressNibbles[1]: &Extension{
								path: addressNibbles[2:50],
								next: &Account{address: common.Address{}, pathLength: 14, info: AccountInfo{common.Nonce{1}, common.Balance{1}, common.Hash{0xAA}},
									storage: &Branch{
										children: Children{
											keyNibbles[0]: &Extension{path: keyNibbles[1:40], next: &Empty{}},
										}}}},
						}}},
			},
			value: common.Value{},
		},
	}

	for name, test := range tests {
		t.Run(name, func(t *testing.T) {
			root, node := ctxt.Build(test.desc)

			proof, err := CreateWitnessProof(ctxt, &root, address, key)
			if err != nil {
				t.Fatalf("failed to create proof: %v", err)
			}

			if !proof.IsValid() {
				t.Fatalf("proof is not valid")
			}

			hash, _ := ctxt.getHashFor(&root)
			gotValue, complete, err := proof.GetState(hash, address, key)
			if err != nil {
				t.Fatalf("failed to get state: %v", err)
			}
			if !complete {
				t.Fatalf("proof is not complete")
			}
			if got, want := gotValue, test.value; got != want {
				t.Errorf("unexpected value: got %v, want %v", got, want)
			}

			if got, want := proof, createReferenceProof(t, ctxt, &root, node); !got.Equals(want) {
				t.Errorf("unexpected proof: got %v, want %v", got, want)
			}
		})
	}
}

func TestCreateWitnessProof_CanCreateProof_EmbeddedNode_Not_In_Proof(t *testing.T) {
	address := common.Address{1}
	key := common.Key{2}
	var value common.Value
	value[20] = 0x02
	value[21] = 0x04

	ctrl := gomock.NewController(t)
	ctxt := newNodeContextWithConfig(t, ctrl, S5LiveConfig)

	desc := &Extension{
		path: AddressToNibblePath(address, ctxt)[0:30],
		next: &Account{address: address, pathLength: 34, info: AccountInfo{Nonce: common.Nonce{0x01}, Balance: common.Balance{0x02}, CodeHash: common.Hash{0x03}},
			storage: &Extension{
				path:         KeyToNibblePath(key, ctxt)[0:40],
				nextEmbedded: true,
				next:         &Tag{label: "V", nested: &Value{key: key, length: 24, value: value}},
			}},
	}

	root, node := ctxt.Build(desc)
	proof, err := CreateWitnessProof(ctxt, &root, address, key, key)
	if err != nil {
		t.Fatalf("failed to create proof: %v", err)
	}

	if got, want := len(proof.proofDb), 3; got != want {
		t.Errorf("unexpected proof size: got %v, want %v", got, want)
	}

	// the hashed rlp of the embedded node should not be a key in the proofDb
	ref, _ := ctxt.Get("V")
	embeddedHash, _ := ctxt.getHashFor(&ref)
	// decode and encode to remove trailing zeros and get RLP of the embedded node.
	decoded, err := rlp.Decode(embeddedHash[:])
	if err != nil {
		t.Fatalf("failed to decode embedded hash: %v", err)
	}
	encoded := rlp.Encode(decoded)
	hash := common.Keccak256(encoded)
	if _, ok := proof.proofDb[hash]; ok {
		t.Errorf("embedded node should not be in the proof")
	}

	refProof := createReferenceProof(t, ctxt, &root, node)
	delete(refProof.proofDb, hash)
	if got, want := proof, refProof; !got.Equals(want) {
		t.Errorf("unexpected proof: got %v, want %v", got, want)
	}
}

func TestCreateWitnessProof_CannotCreateProof_FailingNodeSources(t *testing.T) {
	ctrl := gomock.NewController(t)

	injectedErr := fmt.Errorf("injected error")
	var node Node

	tests := []struct {
		name string
		mock func(*MockNodeSource)
	}{
		{
			name: "call in account proof fails",
			mock: func(mock *MockNodeSource) {
				childId := NewNodeReference(ValueId(123))
				branchNode := BranchNode{}
				branchNode.setEmbedded(0xA, true)
				branchNode.children[0xA] = childId
				mock.EXPECT().getViewAccess(gomock.Any()).Return(shared.MakeShared[Node](&branchNode).GetViewHandle(), nil)
				mock.EXPECT().getViewAccess(gomock.Any()).Return(shared.MakeShared(node).GetViewHandle(), injectedErr)
			},
		},
		{
			name: "call in storage proof fails",
			mock: func(mock *MockNodeSource) {
				var account Node = &AccountNode{address: common.Address{0xA}}
				gomock.InOrder(
					mock.EXPECT().getViewAccess(gomock.Any()).Return(shared.MakeShared(account).GetViewHandle(), nil),
					mock.EXPECT().getViewAccess(gomock.Any()).Return(shared.MakeShared(node).GetViewHandle(), injectedErr),
				)
			},
		},
	}

	hash := common.Hash{0xA}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			nodeSource := NewMockNodeSource(ctrl)
			nodeSource.EXPECT().getConfig().AnyTimes().Return(S5LiveConfig)
			nodeSource.EXPECT().hashKey(gomock.Any()).AnyTimes().Return(hash)
			nodeSource.EXPECT().hashAddress(gomock.Any()).AnyTimes().Return(hash)
			test.mock(nodeSource)
			root := NewNodeReference(EmptyId())

			if _, err := CreateWitnessProof(nodeSource, &root, common.Address{0xA}, common.Key{0x1}); !errors.Is(err, injectedErr) {
				t.Errorf("getting proof should fail")
			}
		})
	}
}

func TestCreateWitnessProof_Serialize_And_Deserialize(t *testing.T) {
	address := common.Address{1}
	key := common.Key{2}
	value := common.Value{3}

	ctrl := gomock.NewController(t)
	ctxt := newNodeContextWithConfig(t, ctrl, S5LiveConfig)

	desc := &Extension{
		path: AddressToNibblePath(address, ctxt)[0:30],
		next: &Account{address: address, pathLength: 34, info: AccountInfo{Nonce: common.Nonce{0x01}, Balance: common.Balance{0x02}, CodeHash: common.Hash{0x03}},
			storage: &Extension{
				path: KeyToNibblePath(key, ctxt)[0:40],
				next: &Value{key: key, length: 24, value: value},
			}},
	}

	root, node := ctxt.Build(desc)
	proof, err := CreateWitnessProof(ctxt, &root, address, key, key)
	if err != nil {
		t.Fatalf("failed to create proof: %v", err)
	}

	referenceProof := createReferenceProof(t, ctxt, &root, node)

	serialized := proof.GetElements()
	if got, want := len(serialized), len(referenceProof.proofDb); got != want {
		t.Fatalf("unexpected serialized proof size: got %v, want %v", got, want)
	}

	recoveredProof := CreateWitnessProofFromNodes(serialized)
	if !recoveredProof.IsValid() {
		t.Errorf("recovered proof is not valid")
	}

	if got, want := recoveredProof, proof; !got.Equals(want) {
		t.Errorf("unexpected proof: got %v, want %v", got, want)
	}
}

func TestCreateWitnessProof_SourceError_All_Paths(t *testing.T) {
	injectedErr := errors.New("injected error")
	address := common.Address{1}

	for _, config := range allMptConfigs {
		t.Run(config.Name, func(t *testing.T) {
			ctrl := gomock.NewController(t)

			ctxt := newNiceNodeContextWithConfig(t, ctrl, config)

			addressNibbles := AddressToNibblePath(address, ctxt)
			desc := &Branch{
				children: Children{
					addressNibbles[0]: &Branch{
						dirtyChildHashes: []int{1},
						children: Children{
							addressNibbles[1]: &Extension{
								path: addressNibbles[2:20],
								next: &Account{address: address, pathLength: 14, info: AccountInfo{common.Nonce{1}, common.Balance{1}, common.Hash{0xAA}},
									storage: &Empty{}}},
						}}}}

			root, _ := ctxt.Build(desc)
			countingSource := errorInjectingNodeManager{ctxt, 999, nil, 0}

			if _, err := CreateWitnessProof(&countingSource, &root, address); err != nil {
				t.Fatalf("unexpected error during iteration: %v", err)
			}

			for i := 1; i < countingSource.counter; i++ {
				ctxt := newNiceNodeContextWithConfig(t, ctrl, config)
				root, _ := ctxt.Build(desc)
				countingSource := errorInjectingNodeManager{ctxt, i, injectedErr, 0}
				if _, err := CreateWitnessProof(&countingSource, &root, address); !errors.Is(err, injectedErr) {
					t.Errorf("expected error %v, got %v, loop: %d, actual: %d", injectedErr, err, i, countingSource.counter)
				}
			}

		})
	}
}

func TestWitnessProof_Extract_and_Merge_Proofs(t *testing.T) {
	ctrl := gomock.NewController(t)

	address1 := common.Address{1}
	address2 := common.Address{2}
	key1 := common.Key{1}
	key2 := common.Key{2}

	ctxt := newNodeContextWithConfig(t, ctrl, S5LiveConfig)

	address1Path := AddressToNibblePath(address1, ctxt)
	address2Path := AddressToNibblePath(address2, ctxt)
	key1Path := KeyToNibblePath(key1, ctxt)
	key2Path := KeyToNibblePath(key2, ctxt)

	// complete tree for the proof
	root, node := ctxt.Build(&Tag{"R", &Branch{
		children: Children{
			address1Path[0]: &Tag{"A_1", &Branch{
				children: Children{
					address1Path[1]: &Tag{"A_2", &Extension{
						path: address1Path[2:50],
						next: &Tag{"A_3", &Account{address: address1, pathLength: 14, info: AccountInfo{common.Nonce{1}, common.Balance{1}, common.Hash{0xAA}},
							storage: &Tag{"K_1", &Branch{
								children: Children{
									key1Path[0]: &Tag{"K_2", &Extension{path: key1Path[1:40],
										next: &Tag{"K_3", &Value{key: key1, length: 24, value: common.Value{0x12}}}}},
									key2Path[0]: &Extension{path: key2Path[1:40],
										next: &Value{key: key2, length: 24, value: common.Value{0x34}}},
								}}},
						}},
					}},
				}}},
			address2Path[0]: &Tag{"B_1", &Branch{
				children: Children{
					address2Path[1]: &Tag{"B_2", &Extension{
						path: address2Path[2:40],
						next: &Tag{"B_3", &Account{address: address2, pathLength: 24, info: AccountInfo{common.Nonce{1}, common.Balance{1}, common.Hash{0xAA}},
							storage: &Branch{
								children: Children{
									key1Path[0]: &Extension{path: key1Path[1:45],
										next: &Value{key: key1, length: 19, value: common.Value{0x12}}},
									key2Path[0]: &Extension{path: key2Path[1:45],
										next: &Value{key: key2, length: 19, value: common.Value{0x34}}},
								},
							},
						}},
					}},
				},
			}},
		}},
	})

	rootHash, _ := ctxt.getHashFor(&root)

	// create following reference proofs
	// 1. proof that contains only nodes for address1 and key1
	// 2. proof that contains only nodes for address2
	// 3. wide proof that includes both previous proofs
	// 4. total proof that includes all nodes in the tree
	address1Key1Proof := createReferenceProofForLabels(t, ctxt, "R", "A_1", "A_2", "A_3", "K_1", "K_2", "K_3")
	address2Proof := createReferenceProofForLabels(t, ctxt, "R", "B_1", "B_2", "B_3")
	wideProof := createReferenceProofForLabels(t, ctxt, "R", "A_1", "A_2", "A_3", "K_1", "K_2", "K_3", "B_1", "B_2", "B_3")
	totalProof := createReferenceProof(t, ctxt, &root, node)

	// make sure extracted proofs are different
	if address1Key1Proof.Equals(address2Proof) {
		t.Fatalf("address1 and address1Key1 proofs are equal")
	}
	if wideProof.Equals(address2Proof) {
		t.Fatalf("total and address1 proofs are equal")
	}
	if wideProof.Equals(address1Key1Proof) {
		t.Fatalf("total and address1Key1Proof proofs are equal")
	}
	if wideProof.Equals(totalProof) {
		t.Fatalf("total and wide proofs are equal")
	}

	t.Run("Extract", func(t *testing.T) {
		// Test proofs can be extracted and that they match the reference proofs
		extractedProofAddress1Key1, complete := totalProof.Extract(rootHash, address1, key1)
		if !complete {
			t.Errorf("proof for %v %v %v not found", rootHash, address1, key1)
		}
		if got, want := extractedProofAddress1Key1, address1Key1Proof; !got.Equals(want) {
			t.Errorf("unexpected proof: got %v, want %v", got, want)
		}

		extractedProofAddress2, complete := totalProof.Extract(rootHash, address2)
		if !complete {
			t.Errorf("proof for %v %v %v not found", rootHash, address1, key1)
		}
		if got, want := extractedProofAddress2, address2Proof; !got.Equals(want) {
			t.Errorf("unexpected proof: got %v, want %v", got, want)
		}
	})

	t.Run("Merge", func(t *testing.T) {
		mergedProof := MergeProofs(address1Key1Proof, address2Proof)
		if got, want := mergedProof, wideProof; !got.Equals(want) {
			t.Errorf("unexpected proof: got %v, want %v", got, want)
		}
	})
}

func TestWitnessProof_Extract_Various_NodeTypes_NotFoundProofs(t *testing.T) {
	ctrl := gomock.NewController(t)

	address := common.Address{0xAB}
	key := common.Key{0x12}

	ctxt := newNodeContextWithConfig(t, ctrl, S5LiveConfig)

	tests := map[string]struct {
		desc NodeDesc
	}{
		"extensionNode wrong path": {&Extension{
			path: AddressToNibblePath(common.Address{1}, ctxt),
			next: &Empty{},
		}},
		"extensionNode to EmptyNode - path exhausted": {&Extension{
			path: AddressToNibblePath(address, ctxt),
			next: &Empty{},
		}},
		"extensionNode to EmptyNode": {&Extension{
			path: AddressToNibblePath(address, ctxt)[0:30],
			next: &Empty{},
		}},
		"extensionNode to extra node": {&Extension{
			path:     AddressToNibblePath(address, ctxt)[0:30],
			nextHash: &common.Hash{}, // test default branch
		}},
		"different accountNode": {&Extension{
			path: AddressToNibblePath(address, ctxt)[0:31],
			next: &Branch{
				children: Children{
					AddressToNibblePath(address, ctxt)[31]: &Account{address: common.Address{1}, pathLength: 40, info: AccountInfo{Nonce: common.Nonce{0x01}, Balance: common.Balance{0x02}, CodeHash: common.Hash{0x03}}},
				}},
		}},
		"valueNode key not found": {&Extension{
			path: AddressToNibblePath(address, ctxt)[0:30],
			next: &Account{address: address, pathLength: 34, info: AccountInfo{Nonce: common.Nonce{0x01}, Balance: common.Balance{0x02}, CodeHash: common.Hash{0x03}},
				storage: &Value{key: common.Key{1}, length: 1, value: common.Value{0x01, 0x02, 0x03, 0x04}},
			},
		}},
	}

	extraProof := make(proofDb)
	extraProof[common.Hash{}] = emptyStringRlpEncoded

	for name, test := range tests {
		t.Run(name, func(t *testing.T) {
			root, node := ctxt.Build(test.desc)
			totalProof := createReferenceProof(t, ctxt, &root, node)

			proofWithEmpty := MergeProofs(totalProof, WitnessProof{extraProof})
			rootHash, _ := ctxt.getHashFor(&root)

			extractedProof, complete := proofWithEmpty.Extract(rootHash, address, key)
			if !complete {
				t.Errorf("proof should be complete")
			}

			// cannot be proven, but the proof must be still complete
			if got, want := extractedProof, totalProof; !got.Equals(want) {
				t.Errorf("unexpected proof: got %v, want %v", got, want)
			}
		})
	}
}

func TestWitnessProof_Extract_Can_Extract_Terminal_Nodes_In_Proof(t *testing.T) {
	ctrl := gomock.NewController(t)
	ctxt := newNodeContextWithConfig(t, ctrl, S5LiveConfig)
	address := common.Address{1}
	nibbles := addressToHashedNibbles(address)

	tests := map[string]struct {
		trie NodeDesc // < the structure of the trie
		path []string // < the path to follow to reach the test account
	}{
		"empty": {
			trie: &Tag{"A", &Empty{}},
			path: []string{},
		},
		"wrong account": {
			trie: &Tag{"A", &Account{}},
			path: []string{"A"},
		},
		"branch without account": {
			trie: &Tag{"A", &Branch{children: Children{
				0x1: &Tag{"B", &Empty{}},
				0x2: &Tag{"C", &Account{address: common.Address{2}}},
			}}},
			path: []string{"A"},
		},
		"branch with wrong account": {
			trie: &Tag{"A", &Branch{children: Children{
				nibbles[0]: &Tag{"B", &Account{address: common.Address{2}, pathLength: 1}},
			}}},
			path: []string{"A", "B"},
		},
		"extension with common prefix lead to empty": {
			trie: &Tag{"A", &Extension{
				path: nibbles[0:63],
				next: &Tag{"B", &Branch{children: Children{
					nibbles[63]: &Tag{"C", &Empty{}},
					0x0:         &Tag{"D", &Account{address: address}},
				}},
				}}},
			path: []string{"A", "B"},
		},
		"extension without common prefix": {
			trie: &Tag{"A", &Extension{path: []Nibble{2, 3}}},
			path: []string{"A"},
		},
		"branch node too deep": {
			trie: &Tag{"A", &Extension{
				path: nibbles, // extension node will exhaust the path
				next: &Tag{"B", &Branch{}},
			}},
			path: []string{"A"},
		},
		"nested branch node too deep": {
			trie: &Tag{"A", &Extension{
				path: nibbles[0:63], // branch node will exhaust the path
				next: &Tag{"B", &Branch{children: Children{
					nibbles[63]: &Tag{"C", &Branch{children: Children{
						0: &Tag{"D", &Account{}},
					}}}}},
				}}},
			path: []string{"A", "B", "C"},
		},
		"account node too deep": {
			trie: &Tag{"A", &Extension{
				path: nibbles[0:63], // branch node will exhaust the path
				next: &Tag{"B", &Branch{children: Children{
					nibbles[63]: &Tag{"C", &Account{address: address, pathLength: 1}}},
				}}},
			},
			path: []string{"A", "B", "C"},
		},
	}

	for name, test := range tests {
		t.Run(name, func(t *testing.T) {
			root, node := ctxt.Build(test.trie)
			totalProof := createReferenceProof(t, ctxt, &root, node)

			expectedProof := createReferenceProofForLabels(t, ctxt, test.path...)

			rootHash, _ := ctxt.getHashFor(&root)

			extractedProof, complete := totalProof.Extract(rootHash, address)
			if !complete {
				t.Errorf("proof should be complete")
			}

			// cannot be proven, but the proof must be still complete
			if got, want := extractedProof, expectedProof; !got.Equals(want) {
				t.Errorf("unexpected proof: got %v, want %v", got, want)
			}
		})
	}
}

func TestWitnessProof_Extract_MissingNode_In_Proof(t *testing.T) {
	ctrl := gomock.NewController(t)

	address := common.Address{0xAB, 0xCD, 0xEF}

	ctxt := newNodeContextWithConfig(t, ctrl, S5LiveConfig)

	desc := &Extension{
		path: AddressToNibblePath(address, ctxt)[0:30],
		next: &Account{address: address, pathLength: 10, info: AccountInfo{Nonce: common.Nonce{0x01}, Balance: common.Balance{0x02}, CodeHash: common.Hash{0x03}}},
	}

	root, node := ctxt.Build(desc)
	totalProof := createReferenceProof(t, ctxt, &root, node)
	rootHash, _ := ctxt.getHashFor(&root)
	// remove a non-root node from the proof
	for k := range totalProof.proofDb {
		if k != rootHash {
			delete(totalProof.proofDb, k)
			break
		}
	}

	if _, exists := totalProof.Extract(rootHash, address); exists {
		t.Fatalf("proof should not exist")
	}
}

func TestWitnessProof_Extract_CorruptedRlp_In_Proof(t *testing.T) {
	ctrl := gomock.NewController(t)

	address := common.Address{0xAB, 0xCD, 0xEF}

	ctxt := newNodeContextWithConfig(t, ctrl, S5LiveConfig)

	desc := &Extension{
		path: AddressToNibblePath(address, ctxt)[0:30],
		next: &Account{address: address, pathLength: 10, info: AccountInfo{Nonce: common.Nonce{0x01}, Balance: common.Balance{0x02}, CodeHash: common.Hash{0x03}}},
	}

	root, node := ctxt.Build(desc)
	totalProof := createReferenceProof(t, ctxt, &root, node)
	rootHash, _ := ctxt.getHashFor(&root)
	// corrupt non-root node in the proof
	for k := range totalProof.proofDb {
		if k != rootHash {
			totalProof.proofDb[k] = []byte{0xAA, 0xBB, 0xCC, 0xDD}
			break
		}
	}

	if _, exists := totalProof.Extract(rootHash, address); exists {
		t.Fatalf("proof should not exist")
	}
}

func TestWitnessProof_Extract_EmbeddedNode_In_Proof(t *testing.T) {
	ctrl := gomock.NewController(t)

	address := common.Address{1}
	key := common.Key{2}
	key2 := common.Key{3}
	var value common.Value
	value[20] = 0x02
	value[21] = 0x04

	ctxt := newNodeContextWithConfig(t, ctrl, S5LiveConfig)

	tests := map[string]struct {
		key      common.Key
		keyFound bool
	}{
		"matching embedded": {
			key:      key,
			keyFound: true,
		},
		"mismatch embedded": {
			key:      key2,
			keyFound: false,
		},
	}

	for name, test := range tests {
		t.Run(name, func(t *testing.T) {
			desc := &Tag{label: "A", nested: &Extension{
				path: AddressToNibblePath(address, ctxt)[0:30],
				next: &Tag{label: "B", nested: &Account{address: address, pathLength: 34, info: AccountInfo{Nonce: common.Nonce{0x01}, Balance: common.Balance{0x02}, CodeHash: common.Hash{0x03}},
					storage: &Tag{label: "C", nested: &Extension{
						path:         KeyToNibblePath(key, ctxt)[0:40],
						nextEmbedded: true,
						next:         &Value{key: test.key, length: 24, value: value},
					}}},
				}}}

			ref, _ := ctxt.Build(desc)
			// proof excludes the embedded node
			totalProof := createReferenceProofForLabels(t, ctxt, "A", "B", "C")
			rootHash, _ := ctxt.getHashFor(&ref)
			proof, complete := totalProof.Extract(rootHash, address, key)
			if got, want := complete, true; got != want {
				t.Errorf("unexpected proof existence: got %v, want %v", got, want)
			}
			if got, want := proof, totalProof; !got.Equals(want) {
				t.Errorf("unexpected proof: got %v, want %v", got, want)
			}
		})
	}

}

func TestWitnessProof_Access_Proof_Fields(t *testing.T) {
	ctrl := gomock.NewController(t)
	address := common.Address{1}
	key := common.Key{2}
	value := common.Value{3}

	ctxt := newNodeContextWithConfig(t, ctrl, S5LiveConfig)

	nonce := common.Nonce{0x01}
	balance := common.Balance{0x02}
	hash := common.Hash{0x03}
	info := AccountInfo{Nonce: nonce, Balance: balance, CodeHash: hash}

	tests := map[string]struct {
		get  func(WitnessProof, common.Hash) (any, bool, error)
		want any
	}{
		"GetAccountInfo": {
			get: func(proof WitnessProof, root common.Hash) (any, bool, error) {
				return proof.GetAccountInfo(root, address)
			},
			want: info,
		},
		"GetNonce": {
			get: func(proof WitnessProof, root common.Hash) (any, bool, error) {
				return proof.GetNonce(root, address)
			},
			want: nonce,
		},
		"GetBalance": {
			get: func(proof WitnessProof, root common.Hash) (any, bool, error) {
				return proof.GetBalance(root, address)
			},
			want: balance,
		},
		"GetCodeHash": {
			get: func(proof WitnessProof, root common.Hash) (any, bool, error) {
				return proof.GetCodeHash(root, address)
			},
			want: hash,
		},
		"GetValue": {
			get: func(proof WitnessProof, root common.Hash) (any, bool, error) {
				return proof.GetState(root, address, key)
			},
			want: value,
		},
	}

	desc := &Extension{
		path: AddressToNibblePath(address, ctxt)[0:30],
		next: &Account{address: address, pathLength: 34, info: info,
			storage: &Extension{
				path: KeyToNibblePath(key, ctxt)[0:40],
				next: &Value{key: key, length: 24, value: value},
			}},
	}

	root, node := ctxt.Build(desc)
	totalProof := createReferenceProof(t, ctxt, &root, node)
	rootHash, _ := ctxt.getHashFor(&root)

	// corrupt non-root node in the proof
	corruptedProof := WitnessProof{maps.Clone(totalProof.proofDb)}
	for k := range corruptedProof.proofDb {
		if k != rootHash {
			corruptedProof.proofDb[k] = []byte{0xAA, 0xBB, 0xCC, 0xDD}
		}
	}

	for name, test := range tests {
		t.Run(name, func(t *testing.T) {
			got, complete, err := test.get(totalProof, rootHash)
			if err != nil {
				t.Fatalf("unexpected error: %v", err)
			}
			if !complete {
				t.Fatalf("proof should be complete")
			}
			if got, want := got, test.want; !reflect.DeepEqual(got, want) {
				t.Errorf("unexpected value: got %v, want %v", got, want)
			}
		})
		t.Run(fmt.Sprintf("%s invalid", name), func(t *testing.T) {
			_, _, err := test.get(corruptedProof, rootHash)
			if err == nil {
				t.Fatalf("expected error")
			}
		})
	}
}

func TestWitnessProof_Access_Proof_Fields_CompleteProofs_EmptyFields_AnotherAddress(t *testing.T) {
	ctrl := gomock.NewController(t)
	address := common.Address{1}
	differentAddress := common.Address{2}
	key := common.Key{2}
	info := AccountInfo{Nonce: common.Nonce{1}, Balance: common.Balance{1}, CodeHash: common.Hash{1}}

	ctxt := newNodeContextWithConfig(t, ctrl, S5LiveConfig)

	testGetters := map[string]struct {
		get  func(*testing.T, WitnessProof, common.Hash, common.Address, common.Key) (any, bool, error)
		want any
	}{
		"GetAccountInfo": {get: func(t *testing.T, proof WitnessProof, rootHash common.Hash, address common.Address, key common.Key) (any, bool, error) {
			return proof.GetAccountInfo(rootHash, address)
		},
			want: AccountInfo{},
		},
		"GetNonce": {get: func(t *testing.T, proof WitnessProof, rootHash common.Hash, address common.Address, key common.Key) (any, bool, error) {
			return proof.GetNonce(rootHash, address)
		},
			want: common.Nonce{},
		},
		"GetBalance": {get: func(t *testing.T, proof WitnessProof, rootHash common.Hash, address common.Address, key common.Key) (any, bool, error) {
			return proof.GetBalance(rootHash, address)
		},
			want: common.Balance{},
		},
		"GetCodeHash": {get: func(t *testing.T, proof WitnessProof, rootHash common.Hash, address common.Address, key common.Key) (any, bool, error) {
			return proof.GetCodeHash(rootHash, address)
		},
			want: common.Hash{},
		},
	}

	testTrees := map[string]NodeDesc{
		"empty": &Empty{},
		"extension to empty": &Extension{
			path: AddressToNibblePath(address, ctxt)[0:30],
			next: &Empty{}},
		"branch to empty": &Branch{
			children: Children{
				AddressToNibblePath(address, ctxt)[0]: &Empty{},
				0x1: &Account{
					address: differentAddress, pathLength: 34, info: info}, // ignored, not to have empty child
			}},
		"account to different": &Extension{
			path: AddressToNibblePath(address, ctxt)[0:30],
			next: &Account{address: differentAddress, pathLength: 34, info: info}},
		"account to empty info": &Extension{
			path: AddressToNibblePath(address, ctxt)[0:30],
			next: &Account{address: address, pathLength: 34, info: AccountInfo{}}},
	}

	for trie, desc := range testTrees {
		for getter, test := range testGetters {
			t.Run(fmt.Sprintf("%s %s", trie, getter), func(t *testing.T) {
				root, node := ctxt.Build(desc)
				totalProof := createReferenceProof(t, ctxt, &root, node)
				rootHash, _ := ctxt.getHashFor(&root)

				got, complete, err := test.get(t, totalProof, rootHash, address, key)
				if err != nil {
					t.Fatalf("unexpected error: %v", err)
				}
				if !complete {
					t.Errorf("proof should be complete")
				}
				if got, want := got, test.want; !reflect.DeepEqual(got, want) {
					t.Errorf("unexpected value: got %v, want %v", got, want)
				}
			})
		}
	}
}

func TestWitnessProof_Access_Proof_Fields_CompleteProofs_EmptyFields_AnotherKey(t *testing.T) {
	ctrl := gomock.NewController(t)
	info := AccountInfo{Nonce: common.Nonce{1}, Balance: common.Balance{1}, CodeHash: common.Hash{1}}
	ctxt := newNodeContextWithConfig(t, ctrl, S5LiveConfig)
	address := common.Address{1}
	value := common.Value{3}

	// The hashes of the following keys have a 4-byte long common prefix.
	var key, differentKey common.Key
	data, _ := hex.DecodeString("965866864f3cc23585ad48a3b4b061c5e1d5a471dbb2360538029046ac528d85")
	copy(key[:], data)
	data, _ = hex.DecodeString("c1bb1e5ab6acf1bef1a125f3d60e0941b9a8624288ffd67282484c25519f9e65")
	copy(differentKey[:], data)

	testTrees := map[string]struct {
		NodeDesc
	}{
		"empty": {&Empty{}},
		"account to different value": {&Extension{
			path: AddressToNibblePath(address, ctxt)[0:31],
			next: &Account{address: address, pathLength: 33, info: info,
				storage: &Extension{
					path: KeyToNibblePath(key, ctxt)[0:41],
					next: &Value{key: differentKey, length: 23, value: value},
				}}}},
		"account to empty path": {&Extension{
			path: AddressToNibblePath(address, ctxt)[0:30],
			next: &Account{address: address, pathLength: 34, info: info,
				storage: &Extension{
					path: KeyToNibblePath(key, ctxt)[0:40],
					next: &Empty{},
				}}}},
		"account to different value - ext/branch node": {&Extension{
			path: AddressToNibblePath(address, ctxt)[0:30],
			next: &Account{address: address, pathLength: 34, info: info,
				storage: &Extension{
					path: KeyToNibblePath(differentKey, ctxt)[0:8],
					next: &Branch{
						children: Children{
							KeyToNibblePath(differentKey, ctxt)[8]: &Value{key: differentKey, length: 56, value: value},
						}}},
			}}},
		"account to different value - ext node": {&Extension{
			path: AddressToNibblePath(address, ctxt)[0:30],
			next: &Account{address: address, pathLength: 34, info: info,
				storage: &Extension{
					path: KeyToNibblePath(differentKey, ctxt)[0:10], // path will differ in ext node
					next: &Value{key: differentKey, length: 54, value: value}},
			}}},
		"account to empty storage": {&Extension{
			path: AddressToNibblePath(address, ctxt)[0:30],
			next: &Account{address: address, pathLength: 34, info: info,
				storage: &Empty{},
			}}},
	}

	for name, desc := range testTrees {
		t.Run(name, func(t *testing.T) {
			root, node := ctxt.Build(desc)
			totalProof := createReferenceProof(t, ctxt, &root, node)
			rootHash, _ := ctxt.getHashFor(&root)

			got, complete, err := totalProof.GetState(rootHash, address, key)

			var empty common.Value
			if got, want := got, empty; got != want {
				t.Errorf("unexpected value: got %v, want %v", got, want)
			}
			if err != nil {
				t.Fatalf("unexpected error: %v", err)
			}
			if !complete {
				t.Fatalf("proof should be complete")
			}
		})
	}
}

func TestWitnessProof_Is_Valid(t *testing.T) {
	ctrl := gomock.NewController(t)

	address := common.Address{0xAB, 0xCD, 0xEF}

	ctxt := newNodeContextWithConfig(t, ctrl, S5LiveConfig)

	desc := &Extension{
		path: AddressToNibblePath(address, ctxt)[0:30],
		next: &Account{address: address, pathLength: 10, info: AccountInfo{Nonce: common.Nonce{0x01}, Balance: common.Balance{0x02}, CodeHash: common.Hash{0x03}}},
	}

	root, node := ctxt.Build(desc)
	totalProof := createReferenceProof(t, ctxt, &root, node)

	t.Run("valid proof", func(t *testing.T) {
		proof := WitnessProof{maps.Clone(totalProof.proofDb)}
		if !proof.IsValid() {
			t.Fatalf("proof should be valid")
		}
	})

	t.Run("hash mismatch", func(t *testing.T) {
		proof := WitnessProof{maps.Clone(totalProof.proofDb)}
		for k := range proof.proofDb {
			proof.proofDb[k] = []byte{0xAA, 0xBB, 0xCC, 0xDD}
		}
		if proof.IsValid() {
			t.Fatalf("proof should be invalid")
		}
	})
	t.Run("corruptedRlp", func(t *testing.T) {
		proof := WitnessProof{maps.Clone(totalProof.proofDb)}
		corruptRlp := []byte{0xAA, 0xBB, 0xCC, 0xDD}
		hash := common.Keccak256(corruptRlp)
		proof.proofDb[hash] = corruptRlp
		if proof.IsValid() {
			t.Fatalf("proof should be invalid")
		}
	})
}

func TestWitnessProof_String(t *testing.T) {
	proof := proofDb{
		common.Hash{0x04}: []byte{0x0D},
		common.Hash{0x02}: []byte{0x0B},
		common.Hash{0x01}: []byte{0x0A},
		common.Hash{0x03}: []byte{0x0C},
	}

	str := "0x0100000000000000000000000000000000000000000000000000000000000000->0x0a\n" +
		"0x0200000000000000000000000000000000000000000000000000000000000000->0x0b\n" +
		"0x0300000000000000000000000000000000000000000000000000000000000000->0x0c\n" +
		"0x0400000000000000000000000000000000000000000000000000000000000000->0x0d\n"

	if got, want := fmt.Sprintf("%s", WitnessProof{proof}), str; got != want {
		t.Errorf("unexpected string: got %v, want %v", got, want)
	}
}

// createReferenceProofForLabels creates a reference witness proof for the given root node.
// The proof is created simply that all nodes in the MPT subtree are stored in the proof.
// Only Empty nodes are excluded.
func createReferenceProofForLabels(t *testing.T, ctxt *nodeContext, labels ...string) WitnessProof {
	t.Helper()
	proof := proofDb{}
	for _, label := range labels {
		_, shared := ctxt.Get(label)
		handle := shared.GetViewHandle()
		node := handle.Get()
		rlp, err := encodeToRlp(node, ctxt, []byte{})
		if err != nil {
			t.Fatalf("failed to encode node: %v", err)
		}
		hash := common.Keccak256(rlp)
		proof[hash] = rlp
		handle.Release()
	}
	return WitnessProof{proof}
}

// createReferenceProof creates a reference witness proof for the given root node.
// The proof is created simply that all nodes in the MPT subtree are stored in the proof.
func createReferenceProof(t *testing.T, ctxt *nodeContext, root *NodeReference, node *shared.Shared[Node]) WitnessProof {
	t.Helper()
	proof := proofDb{}
	handle := node.GetViewHandle()
	_, err := handle.Get().Visit(ctxt, root, 0, MakeVisitor(func(node Node, info NodeInfo) VisitResponse {
		if _, ok := node.(EmptyNode); ok {
			// nodes that are not correct terminal values are not present in the proof
			return VisitResponseContinue
		}
		rlp, err := encodeToRlp(node, ctxt, []byte{})
		if err != nil {
			t.Fatalf("failed to encode node: %v", err)
		}
		hash := common.Keccak256(rlp)
		proof[hash] = rlp
		return VisitResponseContinue
	}))
	handle.Release()

	if err != nil {
		t.Fatalf("failed to create proof: %v", err)
	}
	return WitnessProof{proof}
}

func BenchmarkWitnessProof_CreateProof(b *testing.B) {
	ctrl := gomock.NewController(b)

	address := common.Address{1}
	key := common.Key{2}

	ctxt := newNodeContextWithConfig(b, ctrl, S5LiveConfig)
	addressNibbles := AddressToNibblePath(address, ctxt)
	keyNibbles := KeyToNibblePath(key, ctxt)

	desc := &Branch{
		children: Children{
			addressNibbles[0]: &Branch{
				children: Children{
					addressNibbles[1]: &Extension{
						path: addressNibbles[2:50],
						next: &Account{address: address, pathLength: 14, info: AccountInfo{common.Nonce{1}, common.Balance{1}, common.Hash{0xAA}},
							storage: &Branch{
								children: Children{
									keyNibbles[0]: &Extension{path: keyNibbles[1:40], next: &Value{key: key, length: 24, value: common.Value{0x12}}},
								}}}},
				}}},
	}
	root, _ := ctxt.Build(desc)

	b.ResetTimer()

	var sink bool
	for i := 1; i <= b.N; i++ {
		proof, err := CreateWitnessProof(ctxt, &root, address, key)
		if err != nil {
			b.Fatalf("failed to create proof: %v", err)
		}
		sink = sink || proof.IsValid()
	}

	if !sink {
		b.Fatalf("unexpected result")
	}
}
