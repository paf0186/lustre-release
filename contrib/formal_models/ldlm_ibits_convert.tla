------------------------- MODULE ldlm_ibits_convert -------------------------
(*
 * Model: LDLM IBITS lock conversion race (server-side)
 *
 * Models ldlm_handle_convert0 (ldlm_lockd.c:1625) where the server
 * drops inode bits from a granted lock in response to a client
 * CONVERT request, then calls ldlm_reprocess_all to grant waiters
 * that no longer conflict.
 *
 * IBITS locks have per-bit conflict checking:
 *   - Lock L1 holds {LOOKUP, UPDATE} in PW mode
 *   - Waiter W1 needs UPDATE in PW mode -> conflicts with L1
 *   - Client converts L1: drops UPDATE -> L1 has {LOOKUP} only
 *   - Reprocess: W1 needs UPDATE, L1 has {LOOKUP} -> no conflict
 *   - W1 is granted
 *
 * We model 3 bits: LOOKUP, UPDATE, LAYOUT (simplified)
 * Conflict means: same bit AND incompatible mode.
 * For simplicity, all locks use PW mode (conflicts with PW).
 *
 * Race scenario:
 *   - Convert drops bits under lr_lock, then releases lr_lock
 *     and calls ldlm_reprocess_all
 *   - During the convert handler (between unlock and reprocess),
 *     a new lock W2 arrives for LOOKUP in PW
 *   - Or L1's export disconnects (cancel race)
 *
 * Bug injection:
 *   InjectBugNoReprocess: after convert, skip ldlm_reprocess_all.
 *     Waiters that no longer conflict remain stuck.
 *
 *   InjectBugDropWrongBits: drop the wrong bits (all bits instead
 *     of just the requested ones), simulating a protocol error
 *     where the convert handler clears too many bits.
 *
 * Source (lustre-release master 47638add78):
 *   lustre/ldlm/ldlm_lockd.c     ldlm_handle_convert0 (1625-1708)
 *     CV_Lock: lock_res_and_lock 1657; CANCEL -> ELDLM_NO_LOCK_DATA
 *     1661-1665 (not modeled); CV_DropBits:
 *     ldlm_inodebits_drop(lock, bits & ~new_bits) 1687; CV_Unlock:
 *     1690; CV_Reprocess: ldlm_reprocess_all(res, bits) 1695.
 *     lr_lock is held across the whole bit drop.
 *   lustre/ldlm/ldlm_inodebits.c ldlm_inodebits_drop (475-497)
 *   lustre/ldlm/ldlm_inodebits.c ldlm_reprocess_inodebits_queue
 *     (47-124), the LDLM_IBITS entry of the reprocessing policy
 *     table (ldlm_lock.c:135) -- Reprocessor.
 *   lustre/ldlm/ldlm_lockd.c     ldlm_handle_enqueue (1248-1595)
 *     -- NewEnqueue (was ldlm_handle_enqueue0; renamed by
 *     4435d0121f, LU-14139).
 *
 * Validated against: lustre-release master 47638add78 (2026-09-06)
 *)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    InjectBugNoReprocess,
    InjectBugDropWrongBits

\* Bit definitions (as integers for set operations)
LOOKUP == 1
UPDATE == 2
LAYOUT == 4

AllBits == {LOOKUP, UPDATE, LAYOUT}

(* --algorithm ldlm_ibits_convert

variables
    lr_lock = "free",

    \* L1: granted lock, initially holds LOOKUP + UPDATE
    l1_bits = {LOOKUP, UPDATE},
    l1_active = TRUE,         \* FALSE after cancel

    \* W1: waiter needing UPDATE (conflicts with L1's UPDATE)
    w1_bits_needed = {UPDATE},
    w1_state = "waiting",     \* "waiting", "granted", "none"
    w1_granted_bits = {},

    \* W2: new enqueue needing LOOKUP (arrives during convert)
    w2_bits_needed = {LOOKUP},
    w2_state = "none",        \* "none", "waiting", "granted"
    w2_granted_bits = {},

    \* Reprocess control
    reprocess_pending = FALSE,
    reprocess_done = FALSE;

define
    \* Bit-level conflict: two locks conflict if they share a bit
    \* and have incompatible modes.  Since all locks use PW mode
    \* (which conflicts with PW), two locks conflict on any shared bit.
    BitsConflict(a, b) == a \intersect b /= {}

    \* Check if a waiter can be granted: its needed bits must not
    \* conflict with any granted lock's bits
    CanGrant(needed) ==
        /\ (~l1_active \/ ~BitsConflict(needed, l1_bits))
        \* Also check conflict with other granted waiters
        /\ (w1_state /= "granted" \/ ~BitsConflict(needed, w1_granted_bits))
        /\ (w2_state /= "granted" \/ ~BitsConflict(needed, w2_granted_bits))

    \* ========== SAFETY INVARIANTS ==========

    \* No two granted locks can conflict (share bits in PW mode)
    GrantedNoConflict ==
        /\ (l1_active /\ w1_state = "granted") =>
            ~BitsConflict(l1_bits, w1_granted_bits)
        /\ (l1_active /\ w2_state = "granted") =>
            ~BitsConflict(l1_bits, w2_granted_bits)
        /\ (w1_state = "granted" /\ w2_state = "granted") =>
            ~BitsConflict(w1_granted_bits, w2_granted_bits)

    \* Granted lock bits must be a subset of what was requested
    GrantedBitsValid ==
        /\ (w1_state = "granted") => (w1_granted_bits \subseteq w1_bits_needed)
        /\ (w2_state = "granted") => (w2_granted_bits \subseteq w2_bits_needed)

    \* Terminal: no stuck waiters when convert and enqueue are done
    \* and reprocessor is either done or will never run
    AllDone ==
        /\ pc["convert_handler"] = "Done"
        /\ pc["new_enqueue"] = "Done"
        /\ (pc["reprocessor"] = "Done" \/ ~reprocess_pending)

    NoStuckWaiter ==
        AllDone =>
            /\ (w1_state = "waiting" => ~CanGrant(w1_bits_needed))
            /\ (w2_state = "waiting" => ~CanGrant(w2_bits_needed))

    \* Convert must not drop more bits than requested
    \* After convert, L1 should still have LOOKUP
    ConvertPreservesBits ==
        (pc["convert_handler"] = "Done" /\ l1_active) =>
            l1_bits /= {}

    TypeOK ==
        /\ l1_bits \subseteq AllBits
        /\ w1_bits_needed \subseteq AllBits
        /\ w2_bits_needed \subseteq AllBits
        /\ w1_granted_bits \subseteq AllBits
        /\ w2_granted_bits \subseteq AllBits
        /\ w1_state \in {"waiting", "granted", "none"}
        /\ w2_state \in {"waiting", "granted", "none"}
end define;

\* ================================================================
\* ConvertHandler: Server processes CONVERT request for L1
\* Drops UPDATE bit from L1, triggers reprocess
\* Models: ldlm_handle_convert0 (ldlm_lockd.c:1680-1696)
\* ================================================================
fair process ConvertHandler = "convert_handler"
begin
CV_Lock:
    await lr_lock = "free";
    lr_lock := "convert_handler";

CV_DropBits:
    \* ldlm_inodebits_drop(lock, bits & ~new_bits)
    \* Convert: drop UPDATE, keep LOOKUP
    if InjectBugDropWrongBits then
        \* BUG: drop ALL bits instead of just UPDATE
        l1_bits := {};
    else
        l1_bits := l1_bits \ {UPDATE};
    end if;

CV_Unlock:
    lr_lock := "free";

CV_Reprocess:
    \* ldlm_reprocess_all(lock->l_resource, bits)
    if ~InjectBugNoReprocess then
        reprocess_pending := TRUE;
    end if;
end process;

\* ================================================================
\* Reprocessor: Scans waiting queue after convert drops bits
\* Models: ldlm_reprocess_inodebits_queue in RESCAN mode
\* ================================================================
fair process Reprocessor = "reprocessor"
begin
RP_Wait:
    await reprocess_pending;

RP_Lock:
    await lr_lock = "free";
    lr_lock := "reprocessor";

RP_ScanW1:
    \* Check W1
    if w1_state = "waiting" /\ CanGrant(w1_bits_needed) then
        w1_state := "granted";
        w1_granted_bits := w1_bits_needed;
    end if;

RP_ScanW2:
    \* Check W2
    if w2_state = "waiting" /\ CanGrant(w2_bits_needed) then
        w2_state := "granted";
        w2_granted_bits := w2_bits_needed;
    end if;

RP_Unlock:
    lr_lock := "free";
    reprocess_done := TRUE;
end process;

\* ================================================================
\* NewEnqueue: W2 enqueues for LOOKUP during the convert window
\* Arrives after convert drops bits but possibly before reprocess
\* Models: ldlm_handle_enqueue (ldlm_lockd.c:1248-1595) -> policy check
\* ================================================================
fair process NewEnqueue = "new_enqueue"
begin
NE_Wait:
    \* Wait for convert to have happened (bits dropped)
    await l1_bits /= {LOOKUP, UPDATE};

NE_Lock:
    await lr_lock = "free";
    lr_lock := "new_enqueue";

NE_Enqueue:
    \* ENQUEUE: check granted + waiting queues
    if CanGrant(w2_bits_needed) then
        \* No conflicts -> grant immediately
        \* But also need to check waiting queue: if W1 is waiting
        \* for UPDATE and W2 wants LOOKUP, no conflict (different bits)
        w2_state := "granted";
        w2_granted_bits := w2_bits_needed;
    else
        w2_state := "waiting";
    end if;

NE_Unlock:
    lr_lock := "free";
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES lr_lock, l1_bits, l1_active, w1_bits_needed, w1_state,
          w1_granted_bits, w2_bits_needed, w2_state, w2_granted_bits,
          reprocess_pending, reprocess_done, pc

(* define statement *)
BitsConflict(a, b) == a \intersect b /= {}



CanGrant(needed) ==
    /\ (~l1_active \/ ~BitsConflict(needed, l1_bits))

    /\ (w1_state /= "granted" \/ ~BitsConflict(needed, w1_granted_bits))
    /\ (w2_state /= "granted" \/ ~BitsConflict(needed, w2_granted_bits))




GrantedNoConflict ==
    /\ (l1_active /\ w1_state = "granted") =>
        ~BitsConflict(l1_bits, w1_granted_bits)
    /\ (l1_active /\ w2_state = "granted") =>
        ~BitsConflict(l1_bits, w2_granted_bits)
    /\ (w1_state = "granted" /\ w2_state = "granted") =>
        ~BitsConflict(w1_granted_bits, w2_granted_bits)


GrantedBitsValid ==
    /\ (w1_state = "granted") => (w1_granted_bits \subseteq w1_bits_needed)
    /\ (w2_state = "granted") => (w2_granted_bits \subseteq w2_bits_needed)



AllDone ==
    /\ pc["convert_handler"] = "Done"
    /\ pc["new_enqueue"] = "Done"
    /\ (pc["reprocessor"] = "Done" \/ ~reprocess_pending)

NoStuckWaiter ==
    AllDone =>
        /\ (w1_state = "waiting" => ~CanGrant(w1_bits_needed))
        /\ (w2_state = "waiting" => ~CanGrant(w2_bits_needed))



ConvertPreservesBits ==
    (pc["convert_handler"] = "Done" /\ l1_active) =>
        l1_bits /= {}

TypeOK ==
    /\ l1_bits \subseteq AllBits
    /\ w1_bits_needed \subseteq AllBits
    /\ w2_bits_needed \subseteq AllBits
    /\ w1_granted_bits \subseteq AllBits
    /\ w2_granted_bits \subseteq AllBits
    /\ w1_state \in {"waiting", "granted", "none"}
    /\ w2_state \in {"waiting", "granted", "none"}


vars == << lr_lock, l1_bits, l1_active, w1_bits_needed, w1_state,
           w1_granted_bits, w2_bits_needed, w2_state, w2_granted_bits,
           reprocess_pending, reprocess_done, pc >>

ProcSet == {"convert_handler"} \cup {"reprocessor"} \cup {"new_enqueue"}

Init == (* Global variables *)
        /\ lr_lock = "free"
        /\ l1_bits = {LOOKUP, UPDATE}
        /\ l1_active = TRUE
        /\ w1_bits_needed = {UPDATE}
        /\ w1_state = "waiting"
        /\ w1_granted_bits = {}
        /\ w2_bits_needed = {LOOKUP}
        /\ w2_state = "none"
        /\ w2_granted_bits = {}
        /\ reprocess_pending = FALSE
        /\ reprocess_done = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = "convert_handler" -> "CV_Lock"
                                        [] self = "reprocessor" -> "RP_Wait"
                                        [] self = "new_enqueue" -> "NE_Wait"]

CV_Lock == /\ pc["convert_handler"] = "CV_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "convert_handler"
           /\ pc' = [pc EXCEPT !["convert_handler"] = "CV_DropBits"]
           /\ UNCHANGED << l1_bits, l1_active, w1_bits_needed, w1_state,
                           w1_granted_bits, w2_bits_needed, w2_state,
                           w2_granted_bits, reprocess_pending, reprocess_done >>

CV_DropBits == /\ pc["convert_handler"] = "CV_DropBits"
               /\ IF InjectBugDropWrongBits
                     THEN /\ l1_bits' = {}
                     ELSE /\ l1_bits' = l1_bits \ {UPDATE}
               /\ pc' = [pc EXCEPT !["convert_handler"] = "CV_Unlock"]
               /\ UNCHANGED << lr_lock, l1_active, w1_bits_needed, w1_state,
                               w1_granted_bits, w2_bits_needed, w2_state,
                               w2_granted_bits, reprocess_pending,
                               reprocess_done >>

CV_Unlock == /\ pc["convert_handler"] = "CV_Unlock"
             /\ lr_lock' = "free"
             /\ pc' = [pc EXCEPT !["convert_handler"] = "CV_Reprocess"]
             /\ UNCHANGED << l1_bits, l1_active, w1_bits_needed, w1_state,
                             w1_granted_bits, w2_bits_needed, w2_state,
                             w2_granted_bits, reprocess_pending,
                             reprocess_done >>

CV_Reprocess == /\ pc["convert_handler"] = "CV_Reprocess"
                /\ IF ~InjectBugNoReprocess
                      THEN /\ reprocess_pending' = TRUE
                      ELSE /\ TRUE
                           /\ UNCHANGED reprocess_pending
                /\ pc' = [pc EXCEPT !["convert_handler"] = "Done"]
                /\ UNCHANGED << lr_lock, l1_bits, l1_active, w1_bits_needed,
                                w1_state, w1_granted_bits, w2_bits_needed,
                                w2_state, w2_granted_bits, reprocess_done >>

ConvertHandler == CV_Lock \/ CV_DropBits \/ CV_Unlock \/ CV_Reprocess

RP_Wait == /\ pc["reprocessor"] = "RP_Wait"
           /\ reprocess_pending
           /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Lock"]
           /\ UNCHANGED << lr_lock, l1_bits, l1_active, w1_bits_needed,
                           w1_state, w1_granted_bits, w2_bits_needed, w2_state,
                           w2_granted_bits, reprocess_pending, reprocess_done >>

RP_Lock == /\ pc["reprocessor"] = "RP_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "reprocessor"
           /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_ScanW1"]
           /\ UNCHANGED << l1_bits, l1_active, w1_bits_needed, w1_state,
                           w1_granted_bits, w2_bits_needed, w2_state,
                           w2_granted_bits, reprocess_pending, reprocess_done >>

RP_ScanW1 == /\ pc["reprocessor"] = "RP_ScanW1"
             /\ IF w1_state = "waiting" /\ CanGrant(w1_bits_needed)
                   THEN /\ w1_state' = "granted"
                        /\ w1_granted_bits' = w1_bits_needed
                   ELSE /\ TRUE
                        /\ UNCHANGED << w1_state, w1_granted_bits >>
             /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_ScanW2"]
             /\ UNCHANGED << lr_lock, l1_bits, l1_active, w1_bits_needed,
                             w2_bits_needed, w2_state, w2_granted_bits,
                             reprocess_pending, reprocess_done >>

RP_ScanW2 == /\ pc["reprocessor"] = "RP_ScanW2"
             /\ IF w2_state = "waiting" /\ CanGrant(w2_bits_needed)
                   THEN /\ w2_state' = "granted"
                        /\ w2_granted_bits' = w2_bits_needed
                   ELSE /\ TRUE
                        /\ UNCHANGED << w2_state, w2_granted_bits >>
             /\ pc' = [pc EXCEPT !["reprocessor"] = "RP_Unlock"]
             /\ UNCHANGED << lr_lock, l1_bits, l1_active, w1_bits_needed,
                             w1_state, w1_granted_bits, w2_bits_needed,
                             reprocess_pending, reprocess_done >>

RP_Unlock == /\ pc["reprocessor"] = "RP_Unlock"
             /\ lr_lock' = "free"
             /\ reprocess_done' = TRUE
             /\ pc' = [pc EXCEPT !["reprocessor"] = "Done"]
             /\ UNCHANGED << l1_bits, l1_active, w1_bits_needed, w1_state,
                             w1_granted_bits, w2_bits_needed, w2_state,
                             w2_granted_bits, reprocess_pending >>

Reprocessor == RP_Wait \/ RP_Lock \/ RP_ScanW1 \/ RP_ScanW2 \/ RP_Unlock

NE_Wait == /\ pc["new_enqueue"] = "NE_Wait"
           /\ l1_bits /= {LOOKUP, UPDATE}
           /\ pc' = [pc EXCEPT !["new_enqueue"] = "NE_Lock"]
           /\ UNCHANGED << lr_lock, l1_bits, l1_active, w1_bits_needed,
                           w1_state, w1_granted_bits, w2_bits_needed, w2_state,
                           w2_granted_bits, reprocess_pending, reprocess_done >>

NE_Lock == /\ pc["new_enqueue"] = "NE_Lock"
           /\ lr_lock = "free"
           /\ lr_lock' = "new_enqueue"
           /\ pc' = [pc EXCEPT !["new_enqueue"] = "NE_Enqueue"]
           /\ UNCHANGED << l1_bits, l1_active, w1_bits_needed, w1_state,
                           w1_granted_bits, w2_bits_needed, w2_state,
                           w2_granted_bits, reprocess_pending, reprocess_done >>

NE_Enqueue == /\ pc["new_enqueue"] = "NE_Enqueue"
              /\ IF CanGrant(w2_bits_needed)
                    THEN /\ w2_state' = "granted"
                         /\ w2_granted_bits' = w2_bits_needed
                    ELSE /\ w2_state' = "waiting"
                         /\ UNCHANGED w2_granted_bits
              /\ pc' = [pc EXCEPT !["new_enqueue"] = "NE_Unlock"]
              /\ UNCHANGED << lr_lock, l1_bits, l1_active, w1_bits_needed,
                              w1_state, w1_granted_bits, w2_bits_needed,
                              reprocess_pending, reprocess_done >>

NE_Unlock == /\ pc["new_enqueue"] = "NE_Unlock"
             /\ lr_lock' = "free"
             /\ pc' = [pc EXCEPT !["new_enqueue"] = "Done"]
             /\ UNCHANGED << l1_bits, l1_active, w1_bits_needed, w1_state,
                             w1_granted_bits, w2_bits_needed, w2_state,
                             w2_granted_bits, reprocess_pending,
                             reprocess_done >>

NewEnqueue == NE_Wait \/ NE_Lock \/ NE_Enqueue \/ NE_Unlock

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == ConvertHandler \/ Reprocessor \/ NewEnqueue
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(ConvertHandler)
        /\ WF_vars(Reprocessor)
        /\ WF_vars(NewEnqueue)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
