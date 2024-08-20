#!/bin/bash

# This script is used to test db recovery feature and requires Aida and AidaDb.
# To use this script you need to fill Aida paths under Dynamic variables where
# aida_path is path to Aida root
# aida_db_path is path to AidaDb
# tmp_path is path to tmp directory where database will be created

###########################
#--- Dynamic variables ---#
###########################

# Aida paths
aida_path=''
aida_db_path=''
tmp_path=''

number_of_iterations=$1

if [ -z "$1" ]; then
  echo "Arg 1 not set - Setting number of iterations to 100."
  number_of_iterations=100
fi


# Block variables
first_block=0
last_block=1000
kill_block=900
restore_block=800

##########################
#--- Static variables ---#
##########################

carmen_root=$(cd ../go && pwd)


################
#--- Script ---#
################

# Run the command in the background and redirect stdout and stderr to a log file
log_file="$(pwd)/output.log"
current=$(pwd)

# First iteration has different command
cmd="go run ./cmd/aida-vm-sdb substate --validate --db-tmp "$tmp_path" --carmen-schema 5 --db-impl carmen --aida-db "$aida_db_path" --no-heartbeat-logging --track-progress --archive --archive-variant s5 --archive-query-rate 200 --carmen-cp-interval 200 "$first_block" "$last_block""
cd $aida_path
$cmd &> "$log_file" &
command_pid=$!
cd $current

echo "Creating database with aida-vm-sdb..."

# Function to monitor the log file
monitor_log() {
  tail -F "$log_file" | while read LINE; do
    echo "$LINE" | grep -q "block $kill_block"
    if [ $? -eq 0 ]; then
      echo "Interrupting."
      kill $command_pid
      exit 0
    fi
  done
}

# Start monitoring the log file
monitor_log

# Wait for the first command to complete
wait $command_pid

# Find working dir
working_dir=$(ls -td "$tmp_path"/*/ | head -1)
archive="${working_dir}archive"
live="${working_dir}live"

echo "Testing db created, starting loop."

# Save last working dir to remove it
last_working_dir=""

for ((i=1; i<=number_of_iterations; i++)); do
  # Restore Archive
  (cd $carmen_root && go run ./database/mpt/tool reset --force-unlock "$archive" "$restore_block")

  # Export genesis to restore LiveDB
  genesis="${tmp_path}test_genesis.dat"

  echo "Restoration complete. Exporting LiveDB genesis block "$restore_block"."
  (cd $carmen_root && go run ./database/mpt/tool export --block "$restore_block" "$archive" "$genesis")

  # Restore LiveDB
  echo "Export complete. Applying LiveDB genesis."
  rm -rf "$live"
  (cd $carmen_root && go run ./database/mpt/tool import-live-db "$genesis" "$live")

  echo "Iteration "$i"/"$number_of_iterations""
  first_block=$((restore_block + 1))
  last_block=$((last_block + 1000))
  restore_block=$((restore_block + 1000))
  kill_block=$((kill_block + 1000))

  echo "Syncing to block "$last_block"..."
  command="go run ./cmd/aida-vm-sdb substate --validate --db-tmp "$tmp_path" --carmen-schema 5 --db-impl carmen --aida-db "$aida_db_path" --no-heartbeat-logging --track-progress --archive --archive-variant s5 --archive-query-rate 200 --carmen-cp-interval 200 --db-src "$working_dir" --skip-priming "$first_block" "$last_block""

  cd $aida_path
  $command &> "$log_file" &
  command_pid=$!
  cd $current

  # Start monitoring the log file
  monitor_log

  # Wait for the command to complete
  wait $command_pid

  # Remove unused dir and save current dir to be deleted next iteration.
  echo "Removing previous database"$last_working_dir""
  rm -rf "$last_working_dir"
  last_working_dir="$working_dir"

  # Re-find working dir - Aida copies db-src
  working_dir=$(ls -td "$tmp_path"/*/ | head -1)
  archive="${working_dir}archive"
  live="${working_dir}live"

done

# Clear anything leftover
rm $log_file
rm $working_dir

exit 0