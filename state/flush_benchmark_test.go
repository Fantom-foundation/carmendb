// Copyright (c) 2024 Fantom Foundation
//
// Use of this software is governed by the Business Source License included
// in the LICENSE file and at fantom.foundation/bsl11.
//
// Change Date: 2028-4-16
//
// On the date above, in accordance with the Business Source License, use of
// this software will be governed by the GNU Lesser General Public License v3.

package state

import (
	"github.com/Fantom-foundation/carmendb/common"
	"github.com/Fantom-foundation/carmendb/common/amount"

	"testing"
)

// To run this benchmarks, use the following command:
// go test ./state -run none -bench BenchmarkFlushGoState --benchtime 10s

func BenchmarkFlushGoState(b *testing.B) {
	b.StopTimer()
	dir := b.TempDir()
	state, err := NewState(Parameters{
		Variant:   "go-file",
		Schema:    5,
		Archive:   S5Archive,
		Directory: dir,
	})
	if err != nil {
		b.Fatal(err)
	}
	defer state.Close()

	for n := uint64(0); n < uint64(b.N); n++ {
		update := common.Update{}
		for i := 0; i < 10_000; i++ {
			update.AppendBalanceUpdate(common.Address{
				byte(n >> 24), byte(n >> 16), byte(n >> 8), byte(n),
				byte(i >> 24), byte(i >> 16), byte(i >> 8), byte(i),
			}, amount.New(n))
		}
		err := state.Apply(n, update)
		if err != nil {
			b.Fatal(err)
		}

		b.StartTimer()
		err = state.Flush()
		b.StopTimer()

		if err != nil {
			b.Fatal(err)
		}
	}
}
