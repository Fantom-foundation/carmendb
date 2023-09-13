package mpt

import (
	"errors"
	"fmt"
	"sync"
	"testing"
	"time"

	"github.com/Fantom-foundation/Carmen/go/state/mpt/shared"
	"go.uber.org/mock/gomock"
)

func TestWriteBuffer_CanBeFlushedWhenEmpty(t *testing.T) {
	ctrl := gomock.NewController(t)
	sink := NewMockNodeSink(ctrl)

	buffer := MakeWriteBuffer(sink)
	defer buffer.Close()

	if err := buffer.Flush(); err != nil {
		t.Errorf("failed to flush buffer: %v", err)
	}
}

func TestWriteBuffer_CanFlushASingleElement(t *testing.T) {
	ctrl := gomock.NewController(t)
	sink := NewMockNodeSink(ctrl)

	id := ValueId(12)
	node := shared.MakeShared[Node](EmptyNode{})
	read := node.GetReadHandle()
	sink.EXPECT().Write(id, read)
	read.Release()

	buffer := MakeWriteBuffer(sink)
	defer buffer.Close()

	buffer.Add(id, node)
	if err := buffer.Flush(); err != nil {
		t.Errorf("failed to flush buffer: %v", err)
	}
}

func TestWriteBuffer_CanBeClosedMultipleTimes(t *testing.T) {
	ctrl := gomock.NewController(t)
	sink := NewMockNodeSink(ctrl)

	buffer := MakeWriteBuffer(sink)
	buffer.Close()
	buffer.Close()
}

func TestWriteBuffer_EnqueuedElementCanBeCanceled(t *testing.T) {
	ctrl := gomock.NewController(t)
	sink := NewMockNodeSink(ctrl)

	id := ValueId(12)
	node := shared.MakeShared[Node](EmptyNode{})

	// Since cancel could be too late, a write may happen.
	sink.EXPECT().Write(id, gomock.Any()).MaxTimes(1)

	buffer := MakeWriteBuffer(sink)
	defer buffer.Close()

	buffer.Add(id, node)

	if got, found := buffer.Cancel(id); found && got != node {
		t.Fatalf("failed to cancel %v, wanted %v, got %v, found %v", id, node, got, found)
	}

	if err := buffer.Flush(); err != nil {
		t.Errorf("failed to flush buffer: %v", err)
	}
}

func TestWriteBuffer_CanFlushLargeNumberOfElements(t *testing.T) {
	ctrl := gomock.NewController(t)
	sink := NewMockNodeSink(ctrl)

	N := 1000

	// Setup expectations
	for i := 0; i < N; i++ {
		sink.EXPECT().Write(ValueId(uint64(i)), gomock.Any())
	}

	buffer := makeWriteBuffer(sink, N/10)
	defer buffer.Close()

	// Send in N nodes to be written to the sink.
	node := shared.MakeShared[Node](EmptyNode{})
	for i := 0; i < N; i++ {
		buffer.Add(ValueId(uint64(i)), node)
	}

	if err := buffer.Flush(); err != nil {
		t.Errorf("failed to flush buffer: %v", err)
	}
}

func TestWriteBuffer_AllQueuedEntriesArePresentUntilWritten(t *testing.T) {
	ctrl := gomock.NewController(t)
	sink := NewMockNodeSink(ctrl)

	N := 1000
	buffer := makeWriteBuffer(sink, N/10).(*writeBuffer)
	defer buffer.Close()

	enqueued := map[NodeId]bool{}
	enqueuedLock := sync.Mutex{}

	written := map[NodeId]bool{}

	sink.EXPECT().Write(gomock.Any(), gomock.Any()).AnyTimes().Do(func(id NodeId, _ shared.ReadHandle[Node]) {
		// Check that everything that was enqueued and is not yet written is still present.
		enqueuedLock.Lock()
		for id := range enqueued {
			if _, found := written[id]; !found {
				if !buffer.contains(id) {
					t.Errorf("missing %v in buffer", id)
				}
			}
		}
		enqueuedLock.Unlock()
		written[id] = true
	})

	node := shared.MakeShared[Node](EmptyNode{})
	for i := 0; i < N; i++ {
		id := ValueId(uint64(i))
		buffer.Add(id, node)
		enqueuedLock.Lock()
		enqueued[id] = true
		enqueuedLock.Unlock()
	}

	if err := buffer.Flush(); err != nil {
		t.Errorf("failed to flush buffer: %v", err)
	}
}

func TestWriteBuffer_CheckThatLockedNodesAreWaitedFor(t *testing.T) {
	ctrl := gomock.NewController(t)
	sink := NewMockNodeSink(ctrl)

	id1 := ValueId(1)
	id2 := ValueId(2)
	value1 := shared.MakeShared[Node](EmptyNode{})
	value2 := shared.MakeShared[Node](EmptyNode{})

	read1 := value1.GetReadHandle()
	sink.EXPECT().Write(id1, read1)
	read1.Release()

	read2 := value2.GetReadHandle()
	sink.EXPECT().Write(id2, read2)
	read2.Release()

	buffer := makeWriteBuffer(sink, 100)
	defer buffer.Close()

	write := value2.GetWriteHandle()
	done := false
	go func() {
		time.Sleep(1 * time.Second)
		done = true
		write.Release()
	}()

	buffer.Add(id1, value1)
	buffer.Add(id2, value2)

	if err := buffer.Flush(); err != nil {
		t.Errorf("failed to flush buffer: %v", err)
	}
	if !done {
		t.Errorf("flush finished before write access was released!")
	}
}

func TestWriteBuffer_AFailedFlushIsReported(t *testing.T) {
	ctrl := gomock.NewController(t)
	sink := NewMockNodeSink(ctrl)

	id := ValueId(12)
	node := shared.MakeShared[Node](EmptyNode{})
	read := node.GetReadHandle()
	err := fmt.Errorf("TestError")
	sink.EXPECT().Write(id, read).Return(err)
	read.Release()

	buffer := MakeWriteBuffer(sink)
	defer buffer.Close()

	buffer.Add(id, node)
	if got := buffer.Flush(); !errors.Is(got, err) {
		t.Errorf("sink error was not propagated, wanted %v, got %v", err, got)
	}
}

func TestWriteBuffer_ElementsCanBeAddedInParallel(t *testing.T) {
	// This test checks for race conditions if --race is enabled.
	ctrl := gomock.NewController(t)
	sink := NewMockNodeSink(ctrl)

	N := 1000

	// Setup expectations
	for i := 0; i < N; i++ {
		sink.EXPECT().Write(ValueId(uint64(i)), gomock.Any())
	}

	buffer := makeWriteBuffer(sink, N/10)
	defer buffer.Close()

	// Send in N nodes in parallel.
	node := shared.MakeShared[Node](EmptyNode{})
	var wg sync.WaitGroup
	wg.Add(N / 100)
	for j := 0; j < N/100; j++ {
		go func(j int) {
			defer wg.Done()
			for i := 0; i < 100; i++ {
				buffer.Add(ValueId(uint64(j*100+i)), node)
			}
		}(j)
	}
	wg.Wait()

	if err := buffer.Flush(); err != nil {
		t.Errorf("failed to flush buffer: %v", err)
	}
}

func TestWriteBuffer_ElementsCanBeAddedAndCanceledInParallel(t *testing.T) {
	// This test checks for race conditions if --race is enabled.
	ctrl := gomock.NewController(t)
	sink := NewMockNodeSink(ctrl)

	N := 1000

	sink.EXPECT().Write(gomock.Any(), gomock.Any()).AnyTimes()

	buffer := makeWriteBuffer(sink, N/10)
	defer buffer.Close()

	// Send in N nodes in parallel.
	node := shared.MakeShared[Node](EmptyNode{})
	var wg sync.WaitGroup
	wg.Add(N / 100)
	for j := 0; j < N/100; j++ {
		go func(j int) {
			defer wg.Done()
			for i := 0; i < 100; i++ {
				buffer.Add(ValueId(uint64(j*100+i)), node)
			}
			for i := 0; i < 100; i++ {
				buffer.Cancel(ValueId(uint64(j*100 + i)))
			}
		}(j)
	}
	wg.Wait()

	if err := buffer.Flush(); err != nil {
		t.Errorf("failed to flush buffer: %v", err)
	}
}
