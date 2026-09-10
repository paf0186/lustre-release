#!/bin/bash
# SPDX-License-Identifier: GPL-2.0
#
# run_model.sh - Run TLA+ model checker on Lustre formal models
#
# Usage:
#   ./run_model.sh import_model              # run all cfgs for this model
#   ./run_model.sh import_model --verify-fix 19055  # verify bug/fix pair
#   ./run_model.sh --list-bugs               # list all modeled bugs
#   ./run_model.sh --list-bugs import_model  # list bugs in one model
#   ./run_model.sh --run-cfg path/to/file.cfg  # run a single cfg file
#
# Config files use @metadata tags:
#   \* @model: import_model
#   \* @lu: 19055
#   \* @expect: pass|fail
#   \* @violated: InvariantName
#   \* @timeout: 30m          (override TLC_TIMEOUT for this cfg)
#   \* @states: 10M           (state budget; abort + warn if exceeded)
#   \* @description: Human-readable description
#
# Naming convention:
#   model__LUNNNNN_fix.cfg      - fix for LU-NNNNN (expect: pass)
#   model__LUNNNNN_bug.cfg      - bug reproduction (expect: fail)
#   model__GRNNNNN.cfg          - specific Gerrit change
#   model__baseline.cfg         - no bug injection, general check
#
# Environment:
#   TLC_TIMEOUT    Default timeout per cfg (default: 3600s / 1h)
#                  Accepts: 3600, 60m, 1h
#   TLC_STATES     Default state budget (default: 0 = no limit)
#                  Accepts: 5000000, 5M
#   TLC_WORKERS    TLC worker threads (default: 4)
#   TLA2TOOLS      Path to tla2tools.jar

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TLA2TOOLS="${TLA2TOOLS:-/tmp/tla2tools.jar}"
WORKERS="${TLC_WORKERS:-4}"

# How often to print a progress line (seconds)
PROGRESS_INTERVAL=30
# Warn if state count hasn't changed for this long (seconds)
NO_PROGRESS_WARN=300

die() { echo "ERROR: $*" >&2; exit 1; }

usage() {
	cat <<-'EOF'
	Usage: run_model.sh [OPTIONS] [MODEL_NAME]

	Options:
	  --verify-fix NNNNN   Verify bug/fix pair for LU-NNNNN
	  --list-bugs [MODEL]  List all modeled bugs (optionally for one model)
	  --run-cfg FILE       Run a single cfg file
	  --timeout N          Override default timeout (e.g. 30m, 1h, 3600)
	  --help               Show this help

	Without options, runs all cfg files for the given model.

	Examples:
	  ./run_model.sh import_model
	  ./run_model.sh import_model --verify-fix 19055
	  ./run_model.sh --list-bugs
	  ./run_model.sh --run-cfg clio/TransferPin__GR64440.cfg
	  ./run_model.sh --timeout 10m --run-cfg clio/ClPage__baseline.cfg
	EOF
	exit 0
}

# Find the TLA+ tools jar
find_tla2tools() {
	if [[ -f "$TLA2TOOLS" ]]; then
		return 0
	fi
	for candidate in \
		/tmp/tla2tools.jar \
		"$HOME/tla2tools.jar" \
		/usr/local/lib/tla2tools.jar; do
		if [[ -f "$candidate" ]]; then
			TLA2TOOLS="$candidate"
			return 0
		fi
	done
	die "tla2tools.jar not found. Set TLA2TOOLS env var."
}

# Parse @key: value from a cfg file
# Usage: parse_meta FILE KEY
parse_meta() {
	local file="$1" key="$2"
	grep -oP "(?<=@${key}:\\s).*" "$file" 2>/dev/null | head -1 | \
		sed 's/^[[:space:]]*//;s/[[:space:]]*$//'
}

# Convert a time string to seconds: "30m" -> 1800, "1h" -> 3600, "90" -> 90
to_seconds() {
	local val="$1"
	case "$val" in
	*h)	echo $(( ${val%h} * 3600 )) ;;
	*m)	echo $(( ${val%m} * 60 )) ;;
	*s)	echo $(( ${val%s} )) ;;
	*)	echo "$val" ;;
	esac
}

# Parse a count with optional suffix: "10M" -> 10000000, "500K" -> 500000
parse_count() {
	local val="${1^^}"
	case "$val" in
	*G)	echo $(( ${val%G} * 1000000000 )) ;;
	*M)	echo $(( ${val%M} * 1000000 )) ;;
	*K)	echo $(( ${val%K} * 1000 )) ;;
	*)	echo "$val" ;;
	esac
}

# Format seconds as M:SS
fmt_elapsed() {
	local sec="$1"
	printf "%d:%02d" $(( sec / 60 )) $(( sec % 60 ))
}

# Find cfg files for a model (searches SCRIPT_DIR and subdirs)
find_cfgs_for_model() {
	local model="$1"
	find "$SCRIPT_DIR" -name "${model}__*.cfg" -type f | sort
}

# Find all cfg files with a given LU number
find_cfgs_for_lu() {
	local lu_num="$1"
	local model="$2"  # optional filter

	find "$SCRIPT_DIR" -name "*__*.cfg" -type f | while read -r cfg; do
		local lu
		lu=$(parse_meta "$cfg" "lu")
		[[ -z "$lu" ]] && continue

		# Check if this LU number appears in the @lu field
		# (handles comma-separated lists like "8391, 8246")
		if echo "$lu" | grep -qP "(^|,\\s*)${lu_num}(\\s*,|$)"; then
			if [[ -z "$model" ]] || \
			   [[ "$(parse_meta "$cfg" "model")" == "$model" ]]; then
				echo "$cfg"
			fi
		fi
	done
}

# List all modeled bugs across all models
list_bugs() {
	local model_filter="$1"

	echo "Modeled bugs:"
	echo ""

	# Collect all cfg files with @lu tags
	local cfgs
	if [[ -n "$model_filter" ]]; then
		cfgs=$(find_cfgs_for_model "$model_filter")
	else
		cfgs=$(find "$SCRIPT_DIR" -name "*__*.cfg" -type f | sort)
	fi

	# Deduplicate by model+lu, count pass/fail
	local seen=""
	echo "$cfgs" | while read -r cfg; do
		[[ -z "$cfg" || ! -f "$cfg" ]] && continue
		local lu model
		lu=$(parse_meta "$cfg" "lu")
		[[ -z "$lu" ]] && continue
		model=$(parse_meta "$cfg" "model")

		local key="${model}:${lu}"
		if ! echo "$seen" | grep -qF "$key"; then
			seen="${seen} ${key}"

			# Count pass/fail cfgs for this model+lu
			local pass_count=0 fail_count=0
			while read -r f; do
				[[ -z "$f" || ! -f "$f" ]] && continue
				local e
				e=$(parse_meta "$f" "expect")
				if [[ "$e" == "pass" ]]; then
					((pass_count++))
				elif [[ "$e" == "fail" ]]; then
					((fail_count++))
				fi
			done < <(find_cfgs_for_lu "$lu" "$model")

			local total=$((pass_count + fail_count))
			printf "  LU-%-8s %-25s %d cfgs (%d fail, %d pass)\n" \
				"$lu" "$model" "$total" "$fail_count" "$pass_count"
		fi
	done
}

# Run TLC on a model with a given cfg file.
# Returns 0 on expected result, 1 on unexpected, 2 on timeout/budget.
#
# Progress lines are printed every PROGRESS_INTERVAL seconds.
# Warns if state count stalls for NO_PROGRESS_WARN seconds.
# Aborts early if @states budget is exceeded.
run_tlc() {
	local cfg_file="$1"

	local model expect
	model=$(parse_meta "$cfg_file" "model")
	expect=$(parse_meta "$cfg_file" "expect")

	[[ -z "$model" ]] && die "No @model tag in $cfg_file"
	[[ -z "$expect" ]] && die "No @expect tag in $cfg_file"

	# Per-cfg timeout/budget, falling back to env/global defaults
	local timeout_tag states_tag
	timeout_tag=$(parse_meta "$cfg_file" "timeout")
	states_tag=$(parse_meta "$cfg_file" "states")

	local timeout_sec states_budget
	timeout_sec=$(to_seconds "${timeout_tag:-${TLC_TIMEOUT:-3600}}")
	states_budget=$(parse_count "${states_tag:-${TLC_STATES:-0}}")

	# Find the tla file - could be in same dir or SCRIPT_DIR
	local cfg_dir tla_file
	cfg_dir="$(dirname "$cfg_file")"
	tla_file="${cfg_dir}/${model}.tla"
	[[ -f "$tla_file" ]] || tla_file="${SCRIPT_DIR}/${model}.tla"
	[[ -f "$tla_file" ]] || die "Model not found: ${model}.tla"

	local tla_dir
	tla_dir="$(dirname "$tla_file")"

	local tmpdir tmplog start_time
	tmpdir=$(mktemp -d)
	tmplog=$(mktemp /tmp/tlc.XXXXXX.log)
	start_time=$SECONDS

	# Start TLC in background; all output goes to tmplog
	(cd "$tla_dir" && java -cp "$TLA2TOOLS" \
		tlc2.TLC -config "$cfg_file" "${model}.tla" \
		-workers "$WORKERS" -metadir "$tmpdir" \
		-checkpoint 0 2>&1) > "$tmplog" &
	local tlc_pid=$!

	# Monitor loop: print progress, enforce timeout and state budget
	local last_print_time=0 last_states=0 last_progress_time=$SECONDS
	local timed_out=false budget_exceeded=false

	while kill -0 "$tlc_pid" 2>/dev/null; do
		sleep 5

		local now elapsed
		now=$SECONDS
		elapsed=$(( now - start_time ))

		# Hard timeout
		if (( elapsed >= timeout_sec )); then
			timed_out=true
			kill "$tlc_pid" 2>/dev/null
			break
		fi

		# Rate-limit progress printing
		(( now - last_print_time < PROGRESS_INTERVAL )) && continue
		last_print_time=$now

		# Parse latest state count from TLC progress line
		local progress_line cur_states
		progress_line=$(grep "^Progress" "$tmplog" 2>/dev/null | tail -1)
		[[ -z "$progress_line" ]] && continue

		cur_states=$(echo "$progress_line" | \
			grep -oP '[\d,]+(?= states generated)' | head -1)
		cur_states=${cur_states//,/}
		cur_states=${cur_states:-0}

		printf "    Progress: %'d states (%s elapsed)\n" \
			"$cur_states" "$(fmt_elapsed "$elapsed")"

		# No-progress detection
		if (( cur_states == last_states && last_states > 0 )); then
			local stall=$(( now - last_progress_time ))
			if (( stall >= NO_PROGRESS_WARN )); then
				printf "    WARNING: no new states for %ds" \
					"$stall"
				echo " -- possibly stuck or at fixpoint"
			fi
		else
			last_states=$cur_states
			last_progress_time=$now
		fi

		# State budget
		if (( states_budget > 0 && cur_states > states_budget )); then
			printf "    WARNING: exceeded state budget %'d" \
				"$states_budget"
			printf " (%'d states explored)" "$cur_states"
			echo " -- model may be unbounded; check CONSTANTS"
			budget_exceeded=true
			kill "$tlc_pid" 2>/dev/null
			break
		fi
	done

	wait "$tlc_pid" 2>/dev/null
	local rc=$?

	local elapsed
	elapsed=$(( SECONDS - start_time ))
	local elapsed_fmt
	elapsed_fmt=$(fmt_elapsed "$elapsed")

	# Timeout: report last known state count
	if $timed_out; then
		local last_progress last_count=""
		last_progress=$(grep "^Progress" "$tmplog" 2>/dev/null | tail -1)
		if [[ -n "$last_progress" ]]; then
			last_count=$(echo "$last_progress" | \
				grep -oP '[\d,]+(?= states generated)' | head -1)
		fi
		printf "    TIMEOUT after %s" "$elapsed_fmt"
		[[ -n "$last_count" ]] && \
			printf " (last: %'d states generated)" "$last_count"
		echo ""
		rm -rf "$tmpdir" "$tmplog"
		return 2
	fi

	if $budget_exceeded; then
		rm -rf "$tmpdir" "$tmplog"
		return 2
	fi

	# Normal completion: parse output for result
	local output
	output=$(cat "$tmplog")
	rm -rf "$tmpdir" "$tmplog"

	local states_str
	states_str=$(echo "$output" | \
		grep -oP '[\d,]+ distinct states found' | head -1)

	# TLC errors that mean the model was never checked: the spec or
	# cfg did not parse, or the JVM died.  A non-zero exit here is
	# not a caught bug, whatever @expect says.
	if echo "$output" | grep -qE \
	    -e "Parsing or semantic analysis failed|expecting a keyword" \
	    -e "ConfigFileException|Semantic errors|Unknown operator" \
	    -e "OutOfMemoryError|TLC threw an unexpected exception"; then
		printf "    ERROR - TLC did not check the model (%s)\n" \
			"$elapsed_fmt"
		echo "$output" | grep -E -A3 "^Error:|\*\*\* Errors|Exception" | head -12
		return 1
	fi

	if [[ $rc -eq 0 ]]; then
		# TLC passed (no violation)
		if [[ "$expect" == "fail" ]]; then
			printf "    UNEXPECTED PASS (%s, %s)\n" \
				"$states_str" "$elapsed_fmt"
			echo "    Model did NOT catch the bug!"
			return 1
		else
			printf "    PASS (%s, %s)\n" \
				"$states_str" "$elapsed_fmt"
			return 0
		fi
	else
		# TLC found a violation
		if [[ "$expect" == "fail" ]]; then
			local violation
			if echo "$output" | \
				grep -q "Assert evaluated to FALSE"; then
				violation="Assertion"
			elif echo "$output" | \
				grep -q "Deadlock reached"; then
				violation="Deadlock"
			elif echo "$output" | \
				grep -q "Temporal properties were violated"; then
				violation="Temporal"
			elif echo "$output" | \
				grep -qE "Assumption .* is false"; then
				violation="Assumption"
			else
				violation=$(echo "$output" \
					| grep -oP '(?<=Invariant |Property )\S+' \
					| head -1)
			fi
			if [[ -z "$violation" ]]; then
				printf "    ERROR - TLC exited %d but reported no violation (%s)\n" \
					"$rc" "$elapsed_fmt"
				echo "$output" | grep -E -A2 "^Error:" | head -10
				return 1
			fi
			printf "    CAUGHT BUG (violated: %s, %s)\n" \
				"$violation" "$elapsed_fmt"
			return 0
		else
			printf "    FAIL - unexpected violation! (%s)\n" \
				"$elapsed_fmt"
			echo "$output" | grep -A2 "^Error:" | head -10
			return 1
		fi
	fi
}

# Run all cfgs for a model
run_all() {
	local model="$1"
	local cfgs
	cfgs=$(find_cfgs_for_model "$model")

	[[ -z "$cfgs" ]] && die "No cfg files found for model: $model"

	echo "=== Running all configs for $model ==="
	echo ""

	local all_ok=true
	while read -r cfg; do
		local bname desc expect
		bname=$(basename "$cfg")
		desc=$(parse_meta "$cfg" "description")
		expect=$(parse_meta "$cfg" "expect")
		echo "[$bname] (expect: $expect)"
		[[ -n "$desc" ]] && echo "  $desc"
		if ! run_tlc "$cfg"; then
			all_ok=false
		fi
		echo ""
	done <<< "$cfgs"

	if $all_ok; then
		echo "=== All configs passed expected results ==="
	else
		echo "=== Some configs had unexpected results ==="
		exit 1
	fi
}

# Verify a bug/fix pair for a given LU number
verify_fix() {
	local lu_num="$1"
	local model="$2"  # optional

	local all_cfgs
	all_cfgs=$(find_cfgs_for_lu "$lu_num" "$model")

	[[ -z "$all_cfgs" ]] && die "No cfg files found for LU-${lu_num}"

	echo "=== Verifying fix for LU-${lu_num} ==="
	echo ""

	local all_ok=true
	local found_bug=false found_fix=false

	# Step 1: Bug cfgs (expect: fail)
	echo "Step 1: Inject bug (should be caught)..."
	while read -r cfg; do
		[[ -z "$cfg" || ! -f "$cfg" ]] && continue
		local e
		e=$(parse_meta "$cfg" "expect")
		[[ "$e" != "fail" ]] && continue
		found_bug=true

		local bname desc
		bname=$(basename "$cfg")
		desc=$(parse_meta "$cfg" "description")
		echo "  [$bname] $desc"
		if ! run_tlc "$cfg"; then
			all_ok=false
		fi
	done <<< "$all_cfgs"

	$found_bug || die "No bug cfg (expect: fail) found for LU-${lu_num}"

	# Step 2: Fix cfgs (expect: pass)
	echo "Step 2: Verify fix (should pass)..."
	while read -r cfg; do
		[[ -z "$cfg" || ! -f "$cfg" ]] && continue
		local e
		e=$(parse_meta "$cfg" "expect")
		[[ "$e" != "pass" ]] && continue
		found_fix=true

		local bname desc
		bname=$(basename "$cfg")
		desc=$(parse_meta "$cfg" "description")
		echo "  [$bname] $desc"
		if ! run_tlc "$cfg"; then
			all_ok=false
		fi
	done <<< "$all_cfgs"

	$found_fix || die "No fix cfg (expect: pass) found for LU-${lu_num}"

	echo ""
	if $all_ok; then
		echo "=== VERIFIED: Model catches LU-${lu_num} and fix resolves it ==="
	else
		echo "=== FAILED: Verification incomplete ==="
		exit 1
	fi
}

# Main
main() {
	local model=""
	local bug_num=""
	local mode="run-all"
	local single_cfg=""

	while (( $# > 0 )); do
		case "$1" in
		--verify-fix)
			mode="verify-fix"
			bug_num="$2"
			shift 2
			;;
		--list-bugs)
			mode="list-bugs"
			shift
			;;
		--run-cfg)
			mode="run-cfg"
			single_cfg="$2"
			shift 2
			;;
		--timeout)
			TLC_TIMEOUT=$(to_seconds "$2")
			shift 2
			;;
		--help|-h)
			usage
			;;
		*)
			model="$1"
			shift
			;;
		esac
	done

	find_tla2tools

	case "$mode" in
	list-bugs)
		list_bugs "$model"
		;;

	run-all)
		[[ -n "$model" ]] || \
			die "No model specified. Usage: $0 MODEL_NAME"
		run_all "$model"
		;;

	run-cfg)
		[[ -n "$single_cfg" ]] || die "--run-cfg requires a file path"
		local cfg_path
		if [[ "$single_cfg" == /* ]]; then
			cfg_path="$single_cfg"
		else
			cfg_path="$SCRIPT_DIR/$single_cfg"
		fi
		[[ -f "$cfg_path" ]] || die "Config not found: $cfg_path"

		local bname desc expect
		bname=$(basename "$cfg_path")
		desc=$(parse_meta "$cfg_path" "description")
		expect=$(parse_meta "$cfg_path" "expect")
		echo "[$bname] (expect: $expect)"
		[[ -n "$desc" ]] && echo "  $desc"
		run_tlc "$cfg_path"
		;;

	verify-fix)
		[[ -n "$bug_num" ]] || \
			die "--verify-fix requires a bug number"
		verify_fix "$bug_num" "$model"
		;;
	esac
}

main "$@"
