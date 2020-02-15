------------------------------- MODULE main3 -------------------------------
EXTENDS TLC, Sequences, Integers, FiniteSets

CONSTANTS Workers, Reducer, NULL, ItemRange, ItemCount

ASSUME ItemRange \subseteq Nat
ASSUME ItemCount \in Nat

TupleOf(set, n) == [1..n -> set]


ReduceSet(op(_, _), set, acc) ==
  LET f[s \in SUBSET set] == \* here's where the magic is
    IF s = {} THEN acc
    ELSE LET x == CHOOSE x \in s: TRUE
         IN op(x, f[s \ {x}])
  IN f[set]
  
ReduceSeq(op(_, _), seq, acc) == 
  ReduceSet(LAMBDA i, a: op(seq[i], a), DOMAIN seq, acc)

PossibleInputs == TupleOf(ItemRange, ItemCount)

SumSeq(seq) == ReduceSeq(LAMBDA x, y: x + y, seq, 0)
FairWorkers == CHOOSE set_w \in SUBSET Workers: Cardinality(set_w) = 1
UnfairWorkers == Workers \ FairWorkers

Range(f) == { f[x] : x \in DOMAIN f }

OrderSet(set) == CHOOSE seq \in [1..Cardinality(set) -> set]: Range(seq) = set

SelectSeqByIndex(seq, T(_)) ==
  ReduceSet(LAMBDA i, selected: 
              IF T(i) THEN Append(selected, seq[i]) 
              ELSE selected, 
            DOMAIN seq, <<>>)

Index(seq, elem) == CHOOSE i \in 1..Len(seq): seq[i] = elem

(*--algorithm mapreduce

variables 
    input \in PossibleInputs,
    result = [w \in Workers |-> [total |-> NULL, count |-> NULL]],
    queue = [w \in Workers |-> <<>>],
    status = [w \in Workers |-> "active"];

define
    ActiveWorkers == {w \in Workers: status[w] = "active"}
    HealthyWorkers == {w \in Workers: status[w] /= "broken"}
    TypeInvariant ==
        /\ status \in [Workers -> {"active", "inactive", "broken"}]
        /\ \A w \in Workers:
            /\ Len(queue[w]) <= ItemCount
            /\ \A item \in 1..Len(queue[w]):
                queue[w][item] \in ItemRange
            /\  \/ result[w].total = NULL
                \/ result[w].total <= SumSeq(input)
            /\  \/ result[w].count = NULL
                \/ result[w].count <= ItemCount
end define;

macro reduce() begin
    with w \in {w \in ActiveWorkers: 
        result[w].count = Len(assignments[w])} 
    do
        final[w] := result[w].total;
        status[w] := "inactive";
    end with;
end macro;

procedure work()
    variables total = 0, count = 0;
begin
    WaitForQueue:
        await queue[self] /= <<>>;
    Process:
        while queue[self] /= <<>> do
            total := total + Head(queue[self]);
            queue[self] := Tail(queue[self]);
            count := count + 1;
        end while;
    Result:
        result[self] := [total |-> total, count |-> count];
        goto WaitForQueue;
end procedure;
        
fair process reducer = Reducer
variables final = [w \in Workers |-> 0], assignments = [w \in Workers |-> <<>>];
begin
    Schedule:
        with worker_order = OrderSet(Workers) do
            queue := [w \in Workers |->
                LET offset == Index(worker_order, w) - 1
                IN SelectSeqByIndex(input, LAMBDA i: i % Len(worker_order) = offset)
            ];
            assignments := queue;
        end with;
    ReduceResult:
        while ActiveWorkers /= {} do
            either
                \* Reduce
                reduce();
            or
                \* Reassign
                with from_worker \in ActiveWorkers \ FairWorkers, 
                    to_worker \in HealthyWorkers \ {from_worker}
                do
                    assignments[to_worker] := assignments[to_worker] \o assignments[from_worker];
                    queue[to_worker] := queue[to_worker] \o assignments[from_worker];
                    status[from_worker] := "broken" ||
                    status[to_worker] := "active";
                    final[to_worker] := 0;
                end with;
            end either;
        end while;
    Finish:
        assert SumSeq(final) = SumSeq(input);
end process;

fair process fair_worker \in Workers
variables total = 0;
begin
    FairWorker:
        call work();
end process;

process worker \in UnfairWorkers
variables total = 0;
begin
    RegularWorker:
        call work();
end process;
end algorithm;*)
\* BEGIN TRANSLATION
\* Process variable total of process fair_worker at line 122 col 11 changed to total_
\* Process variable total of process worker at line 129 col 11 changed to total_w
VARIABLES input, result, queue, status, pc, stack

(* define statement *)
ActiveWorkers == {w \in Workers: status[w] = "active"}
HealthyWorkers == {w \in Workers: status[w] /= "broken"}
TypeInvariant ==
    /\ status \in [Workers -> {"active", "inactive", "broken"}]
    /\ \A w \in Workers:
        /\ Len(queue[w]) <= ItemCount
        /\ \A item \in 1..Len(queue[w]):
            queue[w][item] \in ItemRange
        /\  \/ result[w].total = NULL
            \/ result[w].total <= SumSeq(input)
        /\  \/ result[w].count = NULL
            \/ result[w].count <= ItemCount

VARIABLES total, count, final, assignments, total_, total_w

vars == << input, result, queue, status, pc, stack, total, count, final, 
           assignments, total_, total_w >>

ProcSet == {Reducer} \cup (Workers) \cup (UnfairWorkers)

Init == (* Global variables *)
        /\ input \in PossibleInputs
        /\ result = [w \in Workers |-> [total |-> NULL, count |-> NULL]]
        /\ queue = [w \in Workers |-> <<>>]
        /\ status = [w \in Workers |-> "active"]
        (* Procedure work *)
        /\ total = [ self \in ProcSet |-> 0]
        /\ count = [ self \in ProcSet |-> 0]
        (* Process reducer *)
        /\ final = [w \in Workers |-> 0]
        /\ assignments = [w \in Workers |-> <<>>]
        (* Process fair_worker *)
        /\ total_ = [self \in Workers |-> 0]
        (* Process worker *)
        /\ total_w = [self \in UnfairWorkers |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = Reducer -> "Schedule"
                                        [] self \in Workers -> "FairWorker"
                                        [] self \in UnfairWorkers -> "RegularWorker"]

WaitForQueue(self) == /\ pc[self] = "WaitForQueue"
                      /\ queue[self] /= <<>>
                      /\ pc' = [pc EXCEPT ![self] = "Process"]
                      /\ UNCHANGED << input, result, queue, status, stack, 
                                      total, count, final, assignments, total_, 
                                      total_w >>

Process(self) == /\ pc[self] = "Process"
                 /\ IF queue[self] /= <<>>
                       THEN /\ total' = [total EXCEPT ![self] = total[self] + Head(queue[self])]
                            /\ queue' = [queue EXCEPT ![self] = Tail(queue[self])]
                            /\ count' = [count EXCEPT ![self] = count[self] + 1]
                            /\ pc' = [pc EXCEPT ![self] = "Process"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Result"]
                            /\ UNCHANGED << queue, total, count >>
                 /\ UNCHANGED << input, result, status, stack, final, 
                                 assignments, total_, total_w >>

Result(self) == /\ pc[self] = "Result"
                /\ result' = [result EXCEPT ![self] = [total |-> total[self], count |-> count[self]]]
                /\ pc' = [pc EXCEPT ![self] = "WaitForQueue"]
                /\ UNCHANGED << input, queue, status, stack, total, count, 
                                final, assignments, total_, total_w >>

work(self) == WaitForQueue(self) \/ Process(self) \/ Result(self)

Schedule == /\ pc[Reducer] = "Schedule"
            /\ LET worker_order == OrderSet(Workers) IN
                 /\ queue' =          [w \in Workers |->
                                 LET offset == Index(worker_order, w) - 1
                                 IN SelectSeqByIndex(input, LAMBDA i: i % Len(worker_order) = offset)
                             ]
                 /\ assignments' = queue'
            /\ pc' = [pc EXCEPT ![Reducer] = "ReduceResult"]
            /\ UNCHANGED << input, result, status, stack, total, count, final, 
                            total_, total_w >>

ReduceResult == /\ pc[Reducer] = "ReduceResult"
                /\ IF ActiveWorkers /= {}
                      THEN /\ \/ /\ \E w \in        {w \in ActiveWorkers:
                                             result[w].count = Len(assignments[w])}:
                                      /\ final' = [final EXCEPT ![w] = result[w].total]
                                      /\ status' = [status EXCEPT ![w] = "inactive"]
                                 /\ UNCHANGED <<queue, assignments>>
                              \/ /\ \E from_worker \in ActiveWorkers \ FairWorkers:
                                      \E to_worker \in HealthyWorkers \ {from_worker}:
                                        /\ assignments' = [assignments EXCEPT ![to_worker] = assignments[to_worker] \o assignments[from_worker]]
                                        /\ queue' = [queue EXCEPT ![to_worker] = queue[to_worker] \o assignments'[from_worker]]
                                        /\ status' = [status EXCEPT ![from_worker] = "broken",
                                                                    ![to_worker] = "active"]
                                        /\ final' = [final EXCEPT ![to_worker] = 0]
                           /\ pc' = [pc EXCEPT ![Reducer] = "ReduceResult"]
                      ELSE /\ pc' = [pc EXCEPT ![Reducer] = "Finish"]
                           /\ UNCHANGED << queue, status, final, assignments >>
                /\ UNCHANGED << input, result, stack, total, count, total_, 
                                total_w >>

Finish == /\ pc[Reducer] = "Finish"
          /\ Assert(SumSeq(final) = SumSeq(input), 
                    "Failure of assertion at line 118, column 9.")
          /\ pc' = [pc EXCEPT ![Reducer] = "Done"]
          /\ UNCHANGED << input, result, queue, status, stack, total, count, 
                          final, assignments, total_, total_w >>

reducer == Schedule \/ ReduceResult \/ Finish

FairWorker(self) == /\ pc[self] = "FairWorker"
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "work",
                                                             pc        |->  "Done",
                                                             total     |->  total[self],
                                                             count     |->  count[self] ] >>
                                                         \o stack[self]]
                    /\ total' = [total EXCEPT ![self] = 0]
                    /\ count' = [count EXCEPT ![self] = 0]
                    /\ pc' = [pc EXCEPT ![self] = "WaitForQueue"]
                    /\ UNCHANGED << input, result, queue, status, final, 
                                    assignments, total_, total_w >>

fair_worker(self) == FairWorker(self)

RegularWorker(self) == /\ pc[self] = "RegularWorker"
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "work",
                                                                pc        |->  "Done",
                                                                total     |->  total[self],
                                                                count     |->  count[self] ] >>
                                                            \o stack[self]]
                       /\ total' = [total EXCEPT ![self] = 0]
                       /\ count' = [count EXCEPT ![self] = 0]
                       /\ pc' = [pc EXCEPT ![self] = "WaitForQueue"]
                       /\ UNCHANGED << input, result, queue, status, final, 
                                       assignments, total_, total_w >>

worker(self) == RegularWorker(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == reducer
           \/ (\E self \in ProcSet: work(self))
           \/ (\E self \in Workers: fair_worker(self))
           \/ (\E self \in UnfairWorkers: worker(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(reducer)
        /\ \A self \in Workers : WF_vars(fair_worker(self)) /\ WF_vars(work(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
Liveness == <>[](SumSeq(final) = SumSeq(input))

ReducerTerminates == <>[](pc[Reducer] = "Finish")

=============================================================================
\* Modification History
\* Last modified Thu Jan 02 00:43:27 JST 2020 by daioh
\* Created Thu Jan 02 00:42:45 JST 2020 by daioh
