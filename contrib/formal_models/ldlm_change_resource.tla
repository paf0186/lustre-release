------------------------ MODULE ldlm_change_resource ------------------------
(*
 * Model: LDLM parallel lock_change_resource race (LU-18483)
 *
 * Two threads call ldlm_lock_change_resource() concurrently
 * on the same lock.  Both want to change lock->l_resource
 * from R1 to R2.
 *
 * Bug: Both threads read lock->l_resource = R1 (stale read).
 *   Both lock R1+R2, both assign R2, both putref R1.
 *   R1 refcount drops to 0 (double-free / use-after-free).
 *
 * Fix (92b34022d5): RCU read + re-check after locking.
 *   If lock->l_resource changed since the read, another thread
 *   raced -- unlock and retry the while loop.
 *   Also: if oldres == newres, break immediately (no-op).
 *
 * R1 starts at refcount 2 (lock ref + initial ref).
 * R2 starts at refcount 2 (one getref per calling thread).
 * After correct operation: R1 refcount = 1, R2 refcount = 1.
 *
 * Source (lustre-release master 47638add78):
 *   lustre/ldlm/ldlm_lock.c  ldlm_lock_change_resource (520-584)
 *     T*_ReadRes/T*_CheckSame: rcu_dereference(lock->l_resource) 558,
 *     oldres == newres -> break 559-560; T*_Lock: lock both
 *     resources in address order 562-568; T*_Recheck:
 *     lock->l_resource == oldres 569 (else unlock 575-576 and loop);
 *     T*_Swap: rcu_assign_pointer 570; T*_Unlock: 571-572;
 *     T*_Putref: ldlm_resource_putref(oldres) 581.
 *     The early "names already equal" return (531-537) and the
 *     ldlm_resource_get(newres) at 547 (= the initial R2 refs) are
 *     outside the modeled window.
 *   Fix commit 92b34022d5 (LU-18483).
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 *)
EXTENDS Integers, TLC

CONSTANT InjectBugNoRecheck

(* --algorithm ldlm_change_resource

variables
    lock_resource = "R1",
    r1_refcount = 2,
    r2_refcount = 2,
    r1_locked = FALSE,
    r2_locked = FALSE;

define
    \* R1 must never be putref'd more than once
    NoDoublePutref == r1_refcount >= 1

    NoNegativeRefcount ==
        /\ r1_refcount >= 0
        /\ r2_refcount >= 0

    TypeOK ==
        /\ lock_resource \in {"R1", "R2"}
        /\ r1_refcount \in -1..4
        /\ r2_refcount \in -1..4
end define;

fair process Thread1 = "t1"
variables t1_oldres = "none";
begin
T1_ReadRes:
    t1_oldres := lock_resource;
T1_CheckSame:
    \* Fix: if oldres == newres, no work needed
    if ~InjectBugNoRecheck /\ t1_oldres = "R2" then
        \* oldres == newres, just putref oldres (== newres getref)
        r2_refcount := r2_refcount - 1;
        goto T1_Done;
    end if;
T1_Lock:
    await ~r1_locked /\ ~r2_locked;
    r1_locked := TRUE;
    r2_locked := TRUE;
T1_Recheck:
    if ~InjectBugNoRecheck /\ lock_resource /= t1_oldres then
        \* Race: another thread changed it.  Unlock, retry.
        r1_locked := FALSE;
        r2_locked := FALSE;
        t1_oldres := lock_resource;
        goto T1_CheckSame;
    end if;
T1_Swap:
    lock_resource := "R2";
T1_Unlock:
    r1_locked := FALSE;
    r2_locked := FALSE;
T1_Putref:
    \* putref(oldres) -- t1_oldres is what we read
    if t1_oldres = "R1" then
        r1_refcount := r1_refcount - 1;
    else
        r2_refcount := r2_refcount - 1;
    end if;
T1_Done:
    skip;
end process;

fair process Thread2 = "t2"
variables t2_oldres = "none";
begin
T2_ReadRes:
    t2_oldres := lock_resource;
T2_CheckSame:
    if ~InjectBugNoRecheck /\ t2_oldres = "R2" then
        r2_refcount := r2_refcount - 1;
        goto T2_Done;
    end if;
T2_Lock:
    await ~r1_locked /\ ~r2_locked;
    r1_locked := TRUE;
    r2_locked := TRUE;
T2_Recheck:
    if ~InjectBugNoRecheck /\ lock_resource /= t2_oldres then
        r1_locked := FALSE;
        r2_locked := FALSE;
        t2_oldres := lock_resource;
        goto T2_CheckSame;
    end if;
T2_Swap:
    lock_resource := "R2";
T2_Unlock:
    r1_locked := FALSE;
    r2_locked := FALSE;
T2_Putref:
    if t2_oldres = "R1" then
        r1_refcount := r1_refcount - 1;
    else
        r2_refcount := r2_refcount - 1;
    end if;
T2_Done:
    skip;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "d6637e3" /\ chksum(tla) = "3a70bd5d")
VARIABLES lock_resource, r1_refcount, r2_refcount, r1_locked, r2_locked, pc,
          t1_oldres, t2_oldres

(* define statement *)
NoDoublePutref == r1_refcount >= 1

NoNegativeRefcount ==
    /\ r1_refcount >= 0
    /\ r2_refcount >= 0

TypeOK ==
    /\ lock_resource \in {"R1", "R2"}
    /\ r1_refcount \in -1..4
    /\ r2_refcount \in -1..4


vars == << lock_resource, r1_refcount, r2_refcount, r1_locked, r2_locked, pc,
           t1_oldres, t2_oldres >>

ProcSet == {"t1"} \cup {"t2"}

Init == (* Global variables *)
        /\ lock_resource = "R1"
        /\ r1_refcount = 2
        /\ r2_refcount = 2
        /\ r1_locked = FALSE
        /\ r2_locked = FALSE
        (* Process Thread1 *)
        /\ t1_oldres = "none"
        (* Process Thread2 *)
        /\ t2_oldres = "none"
        /\ pc = [self \in ProcSet |-> CASE self = "t1" -> "T1_ReadRes"
                                        [] self = "t2" -> "T2_ReadRes"]

T1_ReadRes == /\ pc["t1"] = "T1_ReadRes"
              /\ t1_oldres' = lock_resource
              /\ pc' = [pc EXCEPT !["t1"] = "T1_CheckSame"]
              /\ UNCHANGED << lock_resource, r1_refcount, r2_refcount,
                              r1_locked, r2_locked, t2_oldres >>

T1_CheckSame == /\ pc["t1"] = "T1_CheckSame"
                /\ IF ~InjectBugNoRecheck /\ t1_oldres = "R2"
                      THEN /\ r2_refcount' = r2_refcount - 1
                           /\ pc' = [pc EXCEPT !["t1"] = "T1_Done"]
                      ELSE /\ pc' = [pc EXCEPT !["t1"] = "T1_Lock"]
                           /\ UNCHANGED r2_refcount
                /\ UNCHANGED << lock_resource, r1_refcount, r1_locked,
                                r2_locked, t1_oldres, t2_oldres >>

T1_Lock == /\ pc["t1"] = "T1_Lock"
           /\ ~r1_locked /\ ~r2_locked
           /\ r1_locked' = TRUE
           /\ r2_locked' = TRUE
           /\ pc' = [pc EXCEPT !["t1"] = "T1_Recheck"]
           /\ UNCHANGED << lock_resource, r1_refcount, r2_refcount, t1_oldres,
                           t2_oldres >>

T1_Recheck == /\ pc["t1"] = "T1_Recheck"
              /\ IF ~InjectBugNoRecheck /\ lock_resource /= t1_oldres
                    THEN /\ r1_locked' = FALSE
                         /\ r2_locked' = FALSE
                         /\ t1_oldres' = lock_resource
                         /\ pc' = [pc EXCEPT !["t1"] = "T1_CheckSame"]
                    ELSE /\ pc' = [pc EXCEPT !["t1"] = "T1_Swap"]
                         /\ UNCHANGED << r1_locked, r2_locked, t1_oldres >>
              /\ UNCHANGED << lock_resource, r1_refcount, r2_refcount,
                              t2_oldres >>

T1_Swap == /\ pc["t1"] = "T1_Swap"
           /\ lock_resource' = "R2"
           /\ pc' = [pc EXCEPT !["t1"] = "T1_Unlock"]
           /\ UNCHANGED << r1_refcount, r2_refcount, r1_locked, r2_locked,
                           t1_oldres, t2_oldres >>

T1_Unlock == /\ pc["t1"] = "T1_Unlock"
             /\ r1_locked' = FALSE
             /\ r2_locked' = FALSE
             /\ pc' = [pc EXCEPT !["t1"] = "T1_Putref"]
             /\ UNCHANGED << lock_resource, r1_refcount, r2_refcount,
                             t1_oldres, t2_oldres >>

T1_Putref == /\ pc["t1"] = "T1_Putref"
             /\ IF t1_oldres = "R1"
                   THEN /\ r1_refcount' = r1_refcount - 1
                        /\ UNCHANGED r2_refcount
                   ELSE /\ r2_refcount' = r2_refcount - 1
                        /\ UNCHANGED r1_refcount
             /\ pc' = [pc EXCEPT !["t1"] = "T1_Done"]
             /\ UNCHANGED << lock_resource, r1_locked, r2_locked, t1_oldres,
                             t2_oldres >>

T1_Done == /\ pc["t1"] = "T1_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["t1"] = "Done"]
           /\ UNCHANGED << lock_resource, r1_refcount, r2_refcount, r1_locked,
                           r2_locked, t1_oldres, t2_oldres >>

Thread1 == T1_ReadRes \/ T1_CheckSame \/ T1_Lock \/ T1_Recheck \/ T1_Swap
              \/ T1_Unlock \/ T1_Putref \/ T1_Done

T2_ReadRes == /\ pc["t2"] = "T2_ReadRes"
              /\ t2_oldres' = lock_resource
              /\ pc' = [pc EXCEPT !["t2"] = "T2_CheckSame"]
              /\ UNCHANGED << lock_resource, r1_refcount, r2_refcount,
                              r1_locked, r2_locked, t1_oldres >>

T2_CheckSame == /\ pc["t2"] = "T2_CheckSame"
                /\ IF ~InjectBugNoRecheck /\ t2_oldres = "R2"
                      THEN /\ r2_refcount' = r2_refcount - 1
                           /\ pc' = [pc EXCEPT !["t2"] = "T2_Done"]
                      ELSE /\ pc' = [pc EXCEPT !["t2"] = "T2_Lock"]
                           /\ UNCHANGED r2_refcount
                /\ UNCHANGED << lock_resource, r1_refcount, r1_locked,
                                r2_locked, t1_oldres, t2_oldres >>

T2_Lock == /\ pc["t2"] = "T2_Lock"
           /\ ~r1_locked /\ ~r2_locked
           /\ r1_locked' = TRUE
           /\ r2_locked' = TRUE
           /\ pc' = [pc EXCEPT !["t2"] = "T2_Recheck"]
           /\ UNCHANGED << lock_resource, r1_refcount, r2_refcount, t1_oldres,
                           t2_oldres >>

T2_Recheck == /\ pc["t2"] = "T2_Recheck"
              /\ IF ~InjectBugNoRecheck /\ lock_resource /= t2_oldres
                    THEN /\ r1_locked' = FALSE
                         /\ r2_locked' = FALSE
                         /\ t2_oldres' = lock_resource
                         /\ pc' = [pc EXCEPT !["t2"] = "T2_CheckSame"]
                    ELSE /\ pc' = [pc EXCEPT !["t2"] = "T2_Swap"]
                         /\ UNCHANGED << r1_locked, r2_locked, t2_oldres >>
              /\ UNCHANGED << lock_resource, r1_refcount, r2_refcount,
                              t1_oldres >>

T2_Swap == /\ pc["t2"] = "T2_Swap"
           /\ lock_resource' = "R2"
           /\ pc' = [pc EXCEPT !["t2"] = "T2_Unlock"]
           /\ UNCHANGED << r1_refcount, r2_refcount, r1_locked, r2_locked,
                           t1_oldres, t2_oldres >>

T2_Unlock == /\ pc["t2"] = "T2_Unlock"
             /\ r1_locked' = FALSE
             /\ r2_locked' = FALSE
             /\ pc' = [pc EXCEPT !["t2"] = "T2_Putref"]
             /\ UNCHANGED << lock_resource, r1_refcount, r2_refcount,
                             t1_oldres, t2_oldres >>

T2_Putref == /\ pc["t2"] = "T2_Putref"
             /\ IF t2_oldres = "R1"
                   THEN /\ r1_refcount' = r1_refcount - 1
                        /\ UNCHANGED r2_refcount
                   ELSE /\ r2_refcount' = r2_refcount - 1
                        /\ UNCHANGED r1_refcount
             /\ pc' = [pc EXCEPT !["t2"] = "T2_Done"]
             /\ UNCHANGED << lock_resource, r1_locked, r2_locked, t1_oldres,
                             t2_oldres >>

T2_Done == /\ pc["t2"] = "T2_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["t2"] = "Done"]
           /\ UNCHANGED << lock_resource, r1_refcount, r2_refcount, r1_locked,
                           r2_locked, t1_oldres, t2_oldres >>

Thread2 == T2_ReadRes \/ T2_CheckSame \/ T2_Lock \/ T2_Recheck \/ T2_Swap
              \/ T2_Unlock \/ T2_Putref \/ T2_Done

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Thread1 \/ Thread2
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Thread1)
        /\ WF_vars(Thread2)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
=============================================================================
