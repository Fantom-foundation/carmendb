package utils

import (
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"testing"

	"github.com/Fantom-foundation/Carmen/go/common"
	"go.uber.org/mock/gomock"
)

func TestCheckpointCoordinator_CanHandleSuccessfulCommit(t *testing.T) {
	ctrl := gomock.NewController(t)
	p1 := NewMockCheckpointParticipant(ctrl)
	p2 := NewMockCheckpointParticipant(ctrl)

	gomock.InOrder(
		p1.EXPECT().GuaranteeCheckpoint(Checkpoint(0)).Return(nil),
		p2.EXPECT().GuaranteeCheckpoint(Checkpoint(0)).Return(nil),
		p1.EXPECT().Prepare(Checkpoint(1)).Return(nil),
		p2.EXPECT().Prepare(Checkpoint(1)).Return(nil),
		p1.EXPECT().Commit(Checkpoint(1)).Return(nil),
		p2.EXPECT().Commit(Checkpoint(1)).Return(nil),
	)

	coordinator, err := NewCheckpointCoordinator(t.TempDir(), p1, p2)
	if err != nil {
		t.Fatalf("failed to create coordinator: %v", err)
	}

	if want, got := Checkpoint(0), coordinator.GetCurrentCheckpoint(); want != got {
		t.Errorf("unexpected last commit: want %d, got %d", want, got)
	}

	commit, err := coordinator.CreateCheckpoint()
	if err != nil {
		t.Errorf("unexpected error: %v", err)
	}

	if want, got := Checkpoint(1), commit; want != got {
		t.Errorf("unexpected last commit: want %d, got %d", want, got)
	}
}

func TestCheckpointCoordinator_CommitIsAbortedIfPreparationFails(t *testing.T) {
	ctrl := gomock.NewController(t)
	p1 := NewMockCheckpointParticipant(ctrl)
	p2 := NewMockCheckpointParticipant(ctrl)

	injectedError := fmt.Errorf("injected error")
	gomock.InOrder(
		p1.EXPECT().GuaranteeCheckpoint(Checkpoint(0)).Return(nil),
		p2.EXPECT().GuaranteeCheckpoint(Checkpoint(0)).Return(nil),
		p1.EXPECT().Prepare(Checkpoint(1)).Return(nil),
		p2.EXPECT().Prepare(Checkpoint(1)).Return(injectedError),
		p1.EXPECT().Abort(Checkpoint(1)).Return(nil),
	)

	coordinator, err := NewCheckpointCoordinator(t.TempDir(), p1, p2)
	if err != nil {
		t.Fatalf("failed to create coordinator: %v", err)
	}

	if want, got := Checkpoint(0), coordinator.GetCurrentCheckpoint(); want != got {
		t.Errorf("unexpected last commit: want %d, got %d", want, got)
	}

	_, err = coordinator.CreateCheckpoint()
	if !errors.Is(err, injectedError) {
		t.Errorf("unexpected error: %v", err)
	}

	if want, got := Checkpoint(0), coordinator.GetCurrentCheckpoint(); want != got {
		t.Errorf("unexpected last commit: want %d, got %d", want, got)
	}
}

func TestCheckpointCoordinator_ErrorsDuringAbortAreCollected(t *testing.T) {
	ctrl := gomock.NewController(t)
	p1 := NewMockCheckpointParticipant(ctrl)
	p2 := NewMockCheckpointParticipant(ctrl)

	injectedCommitError := fmt.Errorf("injected error")
	injectedAbortError := fmt.Errorf("injected error")
	gomock.InOrder(
		p1.EXPECT().GuaranteeCheckpoint(Checkpoint(0)).Return(nil),
		p2.EXPECT().GuaranteeCheckpoint(Checkpoint(0)).Return(nil),
		p1.EXPECT().Prepare(Checkpoint(1)).Return(nil),
		p2.EXPECT().Prepare(Checkpoint(1)).Return(injectedCommitError),
		p1.EXPECT().Abort(Checkpoint(1)).Return(injectedAbortError),
	)

	coordinator, err := NewCheckpointCoordinator(t.TempDir(), p1, p2)
	if err != nil {
		t.Fatalf("failed to create coordinator: %v", err)
	}

	if want, got := Checkpoint(0), coordinator.GetCurrentCheckpoint(); want != got {
		t.Errorf("unexpected last commit: want %d, got %d", want, got)
	}

	_, err = coordinator.CreateCheckpoint()
	if !errors.Is(err, injectedCommitError) {
		t.Errorf("missing injected commit error %v, got: %v", injectedCommitError, err)
	}

	if !errors.Is(err, injectedAbortError) {
		t.Errorf("missing injected abort error %v, got: %v", injectedAbortError, err)
	}

	if want, got := Checkpoint(0), coordinator.GetCurrentCheckpoint(); want != got {
		t.Errorf("unexpected last commit: want %d, got %d", want, got)
	}
}

func TestCheckpointCoordinator_CommitNumberIsPersisted(t *testing.T) {
	dir := t.TempDir()

	for commit := Checkpoint(0); commit < 10; commit++ {
		coordinator, err := NewCheckpointCoordinator(dir)
		if err != nil {
			t.Fatalf("failed to create coordinator: %v", err)
		}
		if want, got := commit, coordinator.GetCurrentCheckpoint(); want != got {
			t.Errorf("unexpected last commit: want %d, got %d", want, got)
		}
		newCommit, err := coordinator.CreateCheckpoint()
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}
		if want, got := commit+1, newCommit; want != got {
			t.Errorf("unexpected last commit: want %d, got %d", want, got)
		}
	}
}

func TestCheckpointCoordinator_ParticipantsAreCheckedForLastCommitNumber(t *testing.T) {
	dir := t.TempDir()

	coordinator, err := NewCheckpointCoordinator(dir)
	if err != nil {
		t.Fatalf("failed to create coordinator: %v", err)
	}
	for i := 0; i < 3; i++ {
		if _, err := coordinator.CreateCheckpoint(); err != nil {
			t.Fatalf("failed to run commit: %v", err)
		}
	}

	ctrl := gomock.NewController(t)
	p1 := NewMockCheckpointParticipant(ctrl)
	p2 := NewMockCheckpointParticipant(ctrl)

	gomock.InOrder(
		p1.EXPECT().GuaranteeCheckpoint(Checkpoint(3)).Return(nil),
		p2.EXPECT().GuaranteeCheckpoint(Checkpoint(3)).Return(nil),
	)

	_, err = NewCheckpointCoordinator(dir, p1, p2)
	if err != nil {
		t.Fatalf("failed to create coordinator: %v", err)
	}
}

func TestCheckpointCoordinator_CreationFailsIfTheProvidedDirectoryLacksWritePermissions(t *testing.T) {
	dir := t.TempDir()

	if _, err := NewCheckpointCoordinator(dir); err != nil {
		t.Fatalf("failed to create coordinator: %v", err)
	}

	info, err := os.Stat(dir)
	if err != nil {
		t.Fatalf("failed to get directory info: %v", err)
	}
	defer os.Chmod(dir, info.Mode())

	if err := os.Chmod(dir, 0500); err != nil {
		t.Fatalf("failed to change permissions: %v", err)
	}
	if _, err := NewCheckpointCoordinator(dir); err == nil {
		t.Errorf("expected coordinator creation to fail since no files can be created in given directory, but it did not")
	}
}

func TestCheckpointCoordinator_CreationFailsIfTheProvidedPathIsNotADirectory(t *testing.T) {
	dir := t.TempDir()

	path := filepath.Join(dir, "file")
	if err := os.WriteFile(path, []byte{}, 0600); err != nil {
		t.Fatalf("failed to create file: %v", err)
	}

	if _, err := NewCheckpointCoordinator(path); err == nil {
		t.Errorf("expected coordinator creation to fail since the provided path is not a directory, but it did not")
	}
}

func TestCheckpointCoordinator_MalformedCommittedCheckPointIsDetected(t *testing.T) {
	dir := t.TempDir()

	// The file is not empty, but it does not contain a valid checkpoint number.
	path := filepath.Join(dir, "committed")
	if err := os.WriteFile(path, []byte{1, 2, 3, 4}, 0600); err != nil {
		t.Fatalf("failed to create file: %v", err)
	}

	if _, err := NewCheckpointCoordinator(dir); err != nil {
		t.Errorf("unexpected error when loading valid commit: %v", err)
	}

	if err := os.WriteFile(path, []byte{1, 2, 3}, 0600); err != nil {
		t.Fatalf("failed to create file: %v", err)
	}

	if _, err := NewCheckpointCoordinator(dir); err == nil {
		t.Errorf("invalid commit number should have been detected, but it was not")
	}
}

func TestCheckpointCoordinator_InconsistentParticipantsAreDetected(t *testing.T) {
	dir := t.TempDir()

	checkpoint := Checkpoint(42)
	if err := createCheckpointFile(filepath.Join(dir, "committed"), checkpoint); err != nil {
		t.Fatalf("failed to write commit: %v", err)
	}

	ctrl := gomock.NewController(t)
	p1 := NewMockCheckpointParticipant(ctrl)
	p2 := NewMockCheckpointParticipant(ctrl)

	gomock.InOrder(
		p1.EXPECT().GuaranteeCheckpoint(checkpoint).Return(nil),
		p2.EXPECT().GuaranteeCheckpoint(checkpoint).Return(errors.New("inconsistent state")),
	)

	if _, err := NewCheckpointCoordinator(dir, p1, p2); err == nil {
		t.Errorf("inconsistent state should have been detected, but it was not")
	}
}

func TestCheckpointCoordinator_FailedCommitLeadsToAbort(t *testing.T) {
	dir := t.TempDir()

	ctrl := gomock.NewController(t)
	participant := NewMockCheckpointParticipant(ctrl)

	gomock.InOrder(
		participant.EXPECT().GuaranteeCheckpoint(Checkpoint(0)),
		participant.EXPECT().Prepare(Checkpoint(1)),
		participant.EXPECT().Abort(Checkpoint(1)),
	)

	coordinator, err := NewCheckpointCoordinator(dir, participant)
	if err != nil {
		t.Fatalf("failed to create coordinator: %v", err)
	}

	// by placing a prepare file with limit access rights into the directory, the prepare will fail
	if err := os.WriteFile(filepath.Join(dir, "prepare"), []byte{}, 0400); err != nil {
		t.Fatalf("failed to create prepare file: %v", err)
	}

	_, err = coordinator.CreateCheckpoint()
	if err == nil {
		t.Fatalf("expected error, but got none")
	}
}

func TestCheckpointCoordinator_FailedCommitOfParticipantLeadsToAnError(t *testing.T) {
	dir := t.TempDir()

	ctrl := gomock.NewController(t)
	participant := NewMockCheckpointParticipant(ctrl)

	injectedError := fmt.Errorf("injected error")
	gomock.InOrder(
		participant.EXPECT().GuaranteeCheckpoint(Checkpoint(0)),
		participant.EXPECT().Prepare(Checkpoint(1)),
		participant.EXPECT().Commit(Checkpoint(1)).Return(injectedError),
	)

	coordinator, err := NewCheckpointCoordinator(dir, participant)
	if err != nil {
		t.Fatalf("failed to create coordinator: %v", err)
	}

	if _, err = coordinator.CreateCheckpoint(); !errors.Is(err, injectedError) {
		t.Fatalf("unexpected error: %v", err)
	}
}

func TestCheckPointCoordinator_RestoreSignalsAllParticipantsToRestoreLastCheckpoint(t *testing.T) {
	dir := t.TempDir()

	checkpoint := Checkpoint(42)
	if err := createCheckpointFile(filepath.Join(dir, "committed"), checkpoint); err != nil {
		t.Fatalf("failed to write commit file: %v", err)
	}

	ctrl := gomock.NewController(t)
	p1 := NewMockCheckpointParticipant(ctrl)
	p2 := NewMockCheckpointParticipant(ctrl)

	gomock.InOrder(
		p1.EXPECT().GuaranteeCheckpoint(checkpoint),
		p2.EXPECT().GuaranteeCheckpoint(checkpoint),
		p1.EXPECT().Restore(checkpoint),
		p2.EXPECT().Restore(checkpoint),
	)

	coordinator, err := NewCheckpointCoordinator(dir, p1, p2)
	if err != nil {
		t.Fatalf("failed to create coordinator: %v", err)
	}

	if err = coordinator.Restore(); err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
}

func TestCheckPointCoordinator_RestoreIssuesAreCollectedAndReported(t *testing.T) {
	dir := t.TempDir()

	ctrl := gomock.NewController(t)
	p1 := NewMockCheckpointParticipant(ctrl)
	p2 := NewMockCheckpointParticipant(ctrl)
	p3 := NewMockCheckpointParticipant(ctrl)
	p4 := NewMockCheckpointParticipant(ctrl)

	checkpoint := Checkpoint(0)
	issue1 := fmt.Errorf("issue 1")
	issue2 := fmt.Errorf("issue 2")
	gomock.InOrder(
		p1.EXPECT().GuaranteeCheckpoint(checkpoint),
		p2.EXPECT().GuaranteeCheckpoint(checkpoint),
		p3.EXPECT().GuaranteeCheckpoint(checkpoint),
		p4.EXPECT().GuaranteeCheckpoint(checkpoint),
		p1.EXPECT().Restore(checkpoint),
		p2.EXPECT().Restore(checkpoint).Return(issue1),
		p3.EXPECT().Restore(checkpoint).Return(issue2),
		p4.EXPECT().Restore(checkpoint),
	)

	coordinator, err := NewCheckpointCoordinator(dir, p1, p2, p3, p4)
	if err != nil {
		t.Fatalf("failed to create coordinator: %v", err)
	}

	err = coordinator.Restore()
	if !errors.Is(err, issue1) {
		t.Errorf("missing issue 1: %v", err)
	}
	if !errors.Is(err, issue2) {
		t.Errorf("missing issue 2: %v", err)
	}
}

type myData interface {
	Get(int) int
	Set(int) int

	GuaranteeCheckpoint(Checkpoint) error // < make sure the state has the given commit it could revert to if needed
	Prepare(Checkpoint) error             // < prepare a commit
	Commit(Checkpoint) error              // < fix a full state that can be restored
	Abort(Checkpoint) error               // < undo a prepared commit
	Restore(Checkpoint) error             // < restore a prepared commit

	Flush() error // < write current state to disk; Problem: this is messing up the last commit
	Close() error // < close the data structure

	// Idea: have 3 sets of files
	//  - the committed configuration (the configuration to be restored; if there was never a commit, this is the empty state)
	//  - the flushed configuration (stored during shutdown, reset during an init)
	//  - the prepared configuration (during a two-phase commit)
}

var _ CheckpointParticipant = myData(nil)
var _ common.FlushAndCloser = myData(nil)
