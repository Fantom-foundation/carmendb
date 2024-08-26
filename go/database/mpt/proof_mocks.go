// Copyright (c) 2024 Fantom Foundation
//
// Use of this software is governed by the Business Source License included
// in the LICENSE file and at fantom.foundation/bsl11.
//
// Change Date: 2028-4-16
//
// On the date above, in accordance with the Business Source License, use of
// this software will be governed by the GNU Lesser General Public License v3.

// Package mpt is a generated GoMock package.
package mpt

import (
	reflect "reflect"

	common "github.com/Fantom-foundation/Carmen/go/common"
	gomock "go.uber.org/mock/gomock"
)

// MockwitnessProofVisitor is a mock of witnessProofVisitor interface.
type MockwitnessProofVisitor struct {
	ctrl     *gomock.Controller
	recorder *MockwitnessProofVisitorMockRecorder
}

// MockwitnessProofVisitorMockRecorder is the mock recorder for MockwitnessProofVisitor.
type MockwitnessProofVisitorMockRecorder struct {
	mock *MockwitnessProofVisitor
}

// NewMockwitnessProofVisitor creates a new mock instance.
func NewMockwitnessProofVisitor(ctrl *gomock.Controller) *MockwitnessProofVisitor {
	mock := &MockwitnessProofVisitor{ctrl: ctrl}
	mock.recorder = &MockwitnessProofVisitorMockRecorder{mock}
	return mock
}

// EXPECT returns an object that allows the caller to indicate expected use.
func (m *MockwitnessProofVisitor) EXPECT() *MockwitnessProofVisitorMockRecorder {
	return m.recorder
}

// Visit mocks base method.
func (m *MockwitnessProofVisitor) Visit(hash common.Hash, rlpNode rlpEncodedNode, node Node, isEmbedded bool) {
	m.ctrl.T.Helper()
	m.ctrl.Call(m, "GetAllChildren", hash, rlpNode, node, isEmbedded)
}

// Visit indicates an expected call of Visit.
func (mr *MockwitnessProofVisitorMockRecorder) Visit(hash, rlpNode, node, isEmbedded any) *gomock.Call {
	mr.mock.ctrl.T.Helper()
	return mr.mock.ctrl.RecordCallWithMethodType(mr.mock, "GetAllChildren", reflect.TypeOf((*MockwitnessProofVisitor)(nil).Visit), hash, rlpNode, node, isEmbedded)
}
