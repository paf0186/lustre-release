#!/bin/bash
# SPDX-License-Identifier: GPL-2.0
#
# Run the rename lock order tests listed in rename_deadlock.list, one suite
# invocation per test, and report each test's outcome against what the
# catalogue expects for the release under test.
#
#   bash rename_deadlock.sh                 every test in the list
#   RD_ONLY="81j 205a" bash rename_deadlock.sh
#   RD_FROM=81x bash rename_deadlock.sh     resume after a restart
#
# A test that leaves the cluster needing a restart says so
# (rename_deadlock_needs_restart); the run stops there, and RD_FROM resumes
# it once the cluster is back.  The exit status is 0 when every test with a
# known expectation matched, 1 when one did not, 2 when a restart is needed.

LUSTRE=${LUSTRE:-$(dirname $0)/..}
. $LUSTRE/tests/test-framework.sh
init_test_env "$@"
# a test's failure is a result here, not a reason to stop
set +e

RD_LIST=${RD_LIST:-$LUSTRE/tests/rename_deadlock.list}
RD_LOGS=${RD_LOGS:-$TMP/rename_deadlock.$(date +%Y%m%d%H%M%S)}
RD_TIMEOUT=${RD_TIMEOUT:-1200}

# the release under test, as the list's columns name it
rd_release() {
	local v

	if do_facet mds1 "$LCTL list_param \
		mdt.*.enable_parallel_rename_remote" > /dev/null 2>&1; then
		echo series
		return
	fi
	v=$(do_facet mds1 "$LCTL get_param -n version" | awk 'NR == 1')
	case $v in
	2.15.*) echo 2.15 ;;
	2.16.*) echo 2.16 ;;
	# maintenance releases below .50, development builds above
	2.17.[0-4][0-9]|2.17.[0-9]) echo 2.17 ;;
	*) echo master ;;
	esac
}

# the outcome class of one test's log, given its error map
rd_outcome() {
	local log=$1
	local map=$2
	local n

	grep -q "^PASS " $log && { echo C; return; }
	grep -q "^SKIP \|: SKIP: " $log && { echo S; return; }
	n=$(grep -oE "FAIL: \([0-9]+\)" $log | head -1 | tr -dc 0-9)
	[[ -n $n ]] || { echo T; return; }
	[[ ,$map, =~ ,$n=([A-Z]), ]] && echo ${BASH_REMATCH[1]} || echo F
}

# whether an outcome is the one expected
rd_match() {
	local exp=$1
	local out=$2

	case $exp in
	\?) echo - ;;
	-) [[ $out == C || $out == N ]] && echo yes || echo NO ;;
	X) [[ $out == X || $out == F ]] && echo yes || echo NO ;;
	*) [[ $out == $exp ]] && echo yes || echo NO ;;
	esac
}

main() {
	local release=$(rd_release)
	local col
	local started=false
	local mismatch=0
	local suite test entry map e15 e16 e17 emaster eseries
	local exp out log m next

	case $release in
	2.15) col=5 ;; 2.16) col=6 ;; 2.17) col=7 ;; master) col=8 ;;
	series) col=9 ;;
	esac
	mkdir -p $RD_LOGS
	rm -f $TMP/rename-deadlock-restart
	[[ -n $RD_FROM ]] || started=true

	echo "release $release; logs in $RD_LOGS"
	printf "%-14s %-5s %-6s %-7s %-8s %s\n" suite test entry outcome \
		expected match
	while read -r suite test entry map e15 e16 e17 emaster eseries; do
		[[ -z $suite || $suite == \#* ]] && continue
		[[ $test == $RD_FROM ]] && started=true
		$started || continue
		[[ -z $RD_ONLY || " $RD_ONLY " == *" $test "* ]] || continue

		log=$RD_LOGS/$suite.$test.log
		ONLY=$test timeout $RD_TIMEOUT bash $LUSTRE/tests/$suite.sh \
			> $log 2>&1 < /dev/null
		out=$(rd_outcome $log $map)
		exp=$(awk -v c=$col '{ print $c }' <<< \
			"$suite $test $entry $map $e15 $e16 $e17 $emaster $eseries")
		m=$(rd_match $exp $out)
		[[ $m == NO ]] && mismatch=1
		printf "%-14s %-5s %-6s %-7s %-8s %s\n" $suite $test $entry \
			$out $exp $m
		if [[ -e $TMP/rename-deadlock-restart ]]; then
			echo "the cluster needs a restart:" \
				"$(cat $TMP/rename-deadlock-restart)"
			next=$(awk -v t=$test '!/^#/ && NF { if (f) { print $2; exit }
				if ($2 == t) f = 1 }' $RD_LIST)
			echo "restart it, then resume with RD_FROM=$next"
			return 2
		fi
	done < $RD_LIST
	return $mismatch
}

main
