(** * The Dalvik Virtual Machine
Add information about the Dalvik VM.
TODO

To formally verify the Dalvik bytecode generation from G-Machine code, we 
implement the PRVM in Coq.

*)

(** ** Verified Dalvik VM Implementation
We now present the Dalvik VM implementation. This process VM is a register 
machine (PVRM) in which the operands of an instruction are loaded into registers
as opposed to stack machines where the operands are loaded on the stack. 
*)

(** *** Behavior
We begin with the general behavior of this machine. The execution of the machine 
proceeds as follows:

%
\begin{itemize}
  \item Load a instruction from the instruction sequence
  \item Process instruction
  \item Loop till End instruction is encountered
\end{itemize}
%
*)

(** We import the required modules. We limit the register 
    machine implementation to the integral datatype, and define it within the
    [Z_scope]. Support for floating point datatype could be achieved by adding 
    floating point variants of each instruction. This addition however does not 
    require changes to the core functionality of the system.
*)

Require Import List.
Require Import Datatypes.
Require Import ZArith.

Open Scope Z_scope.

Module RMImpl.

(** *** Register Machine Components
    The register machine comprise of a list of registers, a list of addresses,
    a stream of instructions, program counter, and a call stack.
    
    There are three distinct types of registers - general 
    purpose registers [V], parameter registers [P], and return value type 
    registers [R]. Arguments to function call are stored in the parameter 
    registers, whereas return value registers hold the value returned from a 
    function call. 
    
    A register is uniquely identified by its type and index. The type [tReg]
    is thus a tuple.

    A value of  type [tRegs] represent the registers in the machine.
*)

Inductive tRegType : Type :=
   | V : tRegType
   | P : tRegType
   | R : tRegType.

Definition tRegIndex := nat.

Inductive tReg : Type := 
   | Reg : tRegType -> tRegIndex -> tReg.

Notation "( type , index )" := (Reg type index).

Definition getRegType (reg : tReg) : tRegType :=
    match reg with
    | (Reg type index) => type
    end.

Definition getRegIndex (reg : tReg) : tRegIndex :=
    match reg with
    | (Reg type index) => index
    end.

Definition tRegs := list tReg.

Definition tAddr := nat.

Definition tAddrs := list tAddr.

Definition tRegVal := Z.

Definition tRegVals := list tRegVal.

(** The register state of the machine is defined by the [tRegState] type. This triple
    contains the values within the general purpose registers, the paramter registers
    and the return value registers.
*)

Inductive tRegState : Type :=
    | RegState : tRegVals-> tRegVals -> tRegVals -> tRegState.

Notation "( gpregs , paramregs , retregs )" := (RegState gpregs paramregs retregs).

Definition getRegVals (type: tRegType) (rs : tRegState) : tRegVals :=
    let 
        (gpregs, paramregs, retregs) := rs
    in
        match type with
        | V => gpregs
        | P => paramregs
        | R => retregs
        end. 

Definition putRegVals (type: tRegType) (newvals : tRegVals) (rs : tRegState) : tRegState :=
    let 
        (gpregs, paramregs, retregs) := rs
    in
        match type with
        | V => (RegState newvals paramregs retregs)
        | P => (RegState gpregs newvals retregs)
        | R => (RegState gpregs paramregs newvals)
        end. 

Definition getGPRegVals (rs : tRegState) : tRegVals :=
    getRegVals V rs.

Definition getParamRegVals (rs : tRegState) : tRegVals :=
    getRegVals P rs.

Definition getRetRegVals (rs : tRegState) : tRegVals :=
    getRegVals R rs.

Definition putGPRegVals (newvals : tRegVals) (rs : tRegState) : tRegState :=
    putRegVals V newvals rs.

Definition putParamRegVals (newvals : tRegVals) (rs : tRegState) : tRegState :=
    putRegVals P newvals rs.

Definition putRetRegVals (newvals : tRegVals) (rs : tRegState) : tRegState :=
    putRegVals R newvals rs.

(** The program counter (PC) is of type [nat] and [tPCVal] represents the 
    corresponding datatype. 
*)

Definition tPCVal := nat.

(**
Before executing a function call the
current call state (a.k.a activation state) is pushed onto a stack denoted by the
type [tCallStateStack]. When the function call returns the saved state is restored.
The saved state comprises of the registers, the values in registers, and the 
program counter value.
*)

Inductive tCallState : Type :=
    | CallState : tRegState -> tPCVal -> tCallState.

Definition tCallStateStack := list tCallState.

Definition UndefinedCallState : tCallState :=
    (CallState (RegState nil nil nil) 0%nat).

(** *** Instruction Set
The instruction set definition for the register machine is a subset of 
the Dalvik VM instruction set and is defined as the Coq inductive type [instr]
defined below. 
*)

Inductive tInstr : Type :=
    | Noop : tInstr
    | Move : tReg -> tReg -> tInstr 
    | Move_result : tReg -> tInstr
    | Const : tReg -> Z -> tInstr
    | Cmp : tReg -> tReg -> tReg -> tInstr
    | If_eq : tReg -> tReg -> tAddr -> tInstr
    | If_eqz : tReg -> tAddr -> tInstr
    | If_nez : tReg -> tAddr -> tInstr
    | If_ne : tReg -> tReg -> tAddr -> tInstr
    | If_lt : tReg -> tReg -> tAddr -> tInstr
    | If_le : tReg -> tReg -> tAddr -> tInstr
    | If_gt : tReg -> tReg -> tAddr -> tInstr
    | If_ge : tReg -> tReg -> tAddr -> tInstr
    | If_gtz : tReg -> tAddr -> tInstr
    | Neg : tReg -> tReg -> tInstr
    | Add : tReg -> tReg -> tReg -> tInstr
    | Sub : tReg -> tReg -> tReg -> tInstr
    | Mul : tReg -> tReg -> tReg -> tInstr
    | Div : tReg -> tReg -> tReg -> tInstr
    | Rem : tReg -> tReg -> tReg -> tInstr
    | And : tReg -> tReg -> tReg -> tInstr
    | Or : tReg -> tReg -> tReg -> tInstr
    | Xor : tReg -> tReg -> tReg -> tInstr
    | Invoke_static : tRegs -> tAddr -> tInstr
    | Ret_void : tInstr
    | Ret_val : tReg -> tInstr
    | Goto : tAddr -> tInstr
    | Halt : tInstr.

(** 
G-Machine bytecode for a program is translated into a list of Dalvik 
instructions represented by [tProgram].
*)

Definition tProgram := list tInstr.

(** *** Register Machine State
The register machine state is represented by a five-tuple consisting of a
register set [rs], a list of addresses (the heap) [adrs], a list of instructions
[ins], a list of values corresponding to the content of each register [rvals],
a program counter [pc], and a stack of states [ss]. A predefined register 
[retval] is set aside for the purpose of storing return values from functions. 
The machine state is a tuple which holds the snapshot of these four elements. 
The type [tRMState] represents the machine state.
*)

Inductive tRMState : Type :=
    | RMState : tRegState
        -> tAddrs 
        -> tProgram 
        -> tPCVal 
        -> tCallStateStack 
        -> tRMState. 

(** We introduce this shorthand notation to represent the machine tuple. 
*)

Notation "( rs , adrs , ins , pc , ss )" := 
    (RMState rs adrs ins pc ss).

(** To access the machine for a read or write operation, we define the accessor
    functions for each of the register machine fields. *)

Definition getRegState (m : tRMState ) : tRegState :=
    match m with
    | (RMState rs adrs ins pc ss) => rs
    end.

Definition getAddrs (m : tRMState ) : tAddrs :=
    match m with
    | (RMState rs adrs ins pc ss) => adrs
    end.       

Definition getProgram (m : tRMState ) : tProgram :=
    match m with
    | (RMState rs adrs ins pc ss) => ins
    end.

Definition getPC (m : tRMState ) : tPCVal :=
    match m with
    | (RMState rs adrs ins pc ss) => pc
    end.
    
Definition getCallSS (m : tRMState ) : tCallStateStack :=
    match m with
    | (RMState rs adrs ins pc ss) => ss
    end.

Definition getCallStateRegState (cs : tCallState) : tRegState :=
    match cs with 
    | (CallState rs pc) => rs
    end.

Definition getCallStatePC (cs : tCallState) : tPCVal :=
    match cs with 
    | (CallState rs pc) => pc
    end.    

Definition getHeadCallStateStack (css : tCallStateStack) : tCallState :=
    hd UndefinedCallState css.

(** The put functions writes back to the registers and updates the 
    machine state. *)
    
Definition putRegState (rs : tRegState ) (m : tRMState ) : tRMState :=
    (rs, getAddrs m, getProgram m, getPC m, getCallSS m).

Definition putProgram (program : tProgram ) (m : tRMState ) : tRMState :=
    (getRegState m, getAddrs m, program, getPC m, getCallSS m).

Definition putAddrs (addrs : tAddrs ) (m : tRMState ) : tRMState :=
    (getRegState m, addrs, getProgram m, getPC m, getCallSS m).

Definition putPC (pc : tPCVal) (m : tRMState) : tRMState :=
    (getRegState m, getAddrs m, getProgram m, pc, getCallSS m).

Definition putCallSS (ss : tCallStateStack) (m : tRMState) : tRMState :=
    (getRegState m, getAddrs m, getProgram m, getPC m, ss).

(** The helper function [incrementPC] steps the program counter by one.
    The auxiliary functions [getRegVal] and [putRegVal] read from and write to
    registers respectively.
*)

Definition incrementPC (m : tRMState) : tRMState :=
    (putPC (S (getPC m)) m).

(** To work with the call state stack, we define the [pushCallState] and [popCallState]
    functions.
*)

Definition pushCallState (cs : tCallState) (css : tCallStateStack) : tCallStateStack :=
    cs :: css.

Definition popCallState (css : tCallStateStack) : tCallStateStack :=
    match css with
    | nil => nil
    | h :: t => t
    end.

(** We define polymorphic [take] and [drop] functions to operate on lists.
*)

Fixpoint take (X:Type) (n: nat) (l:list X) : (list X) := 
  match n with
  | O => nil
  | S n' => match l with
            | nil => nil
            | h :: t => h :: take X n' t
            end
  end.

Eval compute in (take Z 3 (1::2::3::4::5::6::nil)).

Fixpoint drop (X:Type) (n: nat) (l:list X) : (list X) := 
  match n with
  | O => l
  | S n' => match l with
            | nil => nil
            | h :: t => drop X n' t
            end
  end.

Eval compute in (drop Z 3 (1::2::3::4::5::6::nil)).

Eval compute in (app (take Z 3 (1::2::3::4::5::6::nil)) (drop Z 3 (1::2::3::4::5::6::nil))).

Definition getRegVal (r : tReg) (m : tRMState) : tRegVal :=
    nth (getRegIndex r) (getRegVals (getRegType r) (getRegState m)) 0.

Definition putRegVal (r : tReg) (v : tRegVal) (m : tRMState) : tRMState :=
    let 
        regstate := getRegState m
    in
        let
            (type, index) := r
        in
            let
            regvals := getRegVals type regstate
            in
            putRegState 
                (putRegVals 
                    type 
                    (app 
                        (take Z index regvals) 
                        (v :: (drop Z (S index) regvals))
                    )
                    regstate
                ) 
                m.

(** A singular instance of the return value register is defined 
    by [iRetReg].
*)

Definition iRetReg : tReg :=
    (Reg R 0%nat).

Definition getRetVal (m : tRMState ) : tRegVal :=
    getRegVal iRetReg m.

Definition putRetVal (retval : tRegVal) (m : tRMState) : tRMState :=
    putRegVal iRetReg retval m.

(** *** Instruction Set Implementation
We now define the implementation of the register machine instruction set. 
The add instruction puts the result of adding the contents of registers a 
and b into register dest.
*)

Definition add (dest a b: tReg) (m : tRMState) : tRMState :=
    putRegVal dest ((getRegVal a m) + (getRegVal b m)) m.

(** Similarly, the mul instruction multiplies the operands in registers a and b
and writes the value into the dest. *)

Definition mul (dest a b: tReg) (m : tRMState) : tRMState :=
    putRegVal dest ((getRegVal a m) * (getRegVal b m)) m.

(** The move instruction copies the value from src to dest. 
*)

Definition move (dest src : tReg) (m : tRMState) : tRMState :=
    putRegVal dest (getRegVal src m) m.

(** The const instruction loads a value into the dest register. 
*)

Definition const (dest : tReg) (val : Z) (m : tRMState) : tRMState :=
    putRegVal dest val m.

(** The noop instruction increments the value of the program counter. 
*)

Definition noop (m : tRMState) : tRMState :=
    incrementPC m.

(** Once the machine returns from a function call, the call state is 
    restored back by assigning the value of PC to the one pushed on the 
    call-state stack alongwith with the values of registers.
*)
    
Definition restoreCallState (m : tRMState) : tRMState :=
    let css :=
        getCallSS m
    in
        let cs := 
            getHeadCallStateStack css
        in
            putCallSS 
                (popCallState css)
                (putPC
                    (S (getCallStatePC cs))
                    (putRegState
                        (getCallStateRegState cs)
                        m
                    )
                ). 

(** Once the body of a method is executed, the control is transferred back to
    the calling code using the %\textbf{ret\textit{Type}}% instruction. If the
    method returns a value to the caller, the [ret_val] instruction is executed,
    which puts the value in the argument register into the predefined [retval]
    register of the machine. Once the control is transferred back to the calling
    code, the [move-result] instruction is used to load the value from the 
    [retval] register into an argument register %\cite{Dalvik}%.
*)

Definition ret_void (m : tRMState) : tRMState :=
    let cs := 
        getHeadCallStateStack (getCallSS m)
    in 
        restoreCallState m.

Definition ret_val (r : tReg) (m : tRMState) : tRMState :=
    let rval := 
        getRegVal r m
    in
        let cs := 
            getHeadCallStateStack (getCallSS m)
        in
            putRetVal rval (restoreCallState m).

Definition move_result (dest : tReg) (m : tRMState) : tRMState :=
    putRegVal dest (getRetVal m) m.

(** The [ifeq] implementation is defined as follows: 
    if the value of the register r1 matches r2 then the value of the program 
    counter (PC) is updated with the value given by label, otherwise the value 
    of PC is incremented. 

    Instead of a if-then-else construct, we model the 
    equality check of the two register values with a match on the difference.
    This seemingly circumlocutary construct makes up for the lack of a 
    integer equality operator. 
*)

Definition ifeq (r1 r2: tReg) (label: tAddr) (m : tRMState) : tRMState :=
    match ((getRegVal r1 m) - (getRegVal r2 m)) with
    | 0 => putPC label m 
    | _ => incrementPC m
    end.

Definition ifgtz (r1 : tReg) (label: tAddr) (m : tRMState) : tRMState :=
    let
        val := (getRegVal r1 m)
    in
        match (val - 0) with
        | 0 => incrementPC m
        | _ => putPC label m
        end.

(** We implement the %\textbf{invoke-static}% instruction of the Dalvik VM. This
    instruction allows us to call any function that have been translated from
    %\textbf{H}% into the register machine bytecode.
*)

Definition saveCallState (m : tRMState) : tRMState :=
    putCallSS 
        (pushCallState 
            (CallState (getRegState m) (getPC m))
            (getCallSS m)
        ) 
        m.

Fixpoint loadRegVals (regs: tRegs) (m : tRMState) : tRegVals :=
    match regs with
    | nil => nil
    | r :: rs => (getRegVal r m) :: loadRegVals rs m
    end.

Definition invoke_static (regs: tRegs) (label: tAddr) (m: tRMState) : tRMState :=
    let
        m' := (saveCallState m)
    in
        (putPC 
            label
            (putRegState
                (putParamRegVals 
                    (loadRegVals regs m')
                    (getRegState m')
                )
                m'
            )
        ).
        
Definition goto (label : tAddr) (m : tRMState) : tRMState :=
    putPC label m.        

(** Once we have defined the implementation of the instructions, we are left 
    with defining the state transition mechanics of the register machine itself. 
    The operation of a register machine can be described as a 
    fetch-decode-execute-loop cycle.
    
    We begin with the [fetch] operation. As the name suggests, fetch gets the next
    instruction that is to be executed. It does so by taking a machine state, 
    retrieving the instruction at the address pointed by the value in PC and 
    returning it. 
*)

Definition fetch (m : tRMState) : tInstr :=
    nth (getPC m) (getProgram m) Noop.

(** The [decode] step in this machine is not required, and we proceed to define the 
    [execute] step. The [execute] step takes an instruction, an input machine state, 
    calls the appropriate instruction handler and returns the resulting machine 
    state after the instruction has been processed.
*)

Definition execute (i : tInstr) (m : tRMState) : tRMState :=
    match i with
    | Const r v => incrementPC (const r v m)
    | Move r1 r2 => incrementPC (move r1 r2 m)
    | Move_result r1 => incrementPC (move_result r1 m)
    | Add a b dest => incrementPC (add a b dest m)
    | Mul a b dest => incrementPC (mul a b dest m)
    | Noop => noop m
    | If_eq r1 r2 label => ifeq r1 r2 label m
    | If_gtz r1 label => ifgtz r1 label m
    | Invoke_static regs label => invoke_static regs label m
    | Ret_void => ret_void m
    | Ret_val r => ret_val r m
    | Goto label => goto label m
    | _ => m
    end.

(** ** Program Termination State
    We model the termination state of the machine by the special marker 
    [haltState]. In this state we preserve the values within the
    registers and wipe out all other state data.
*)

Definition haltState (m : tRMState) : tRMState :=
    (getRegState m, (nil), getProgram m, getPC m, (nil)).

(** During a single step, we fetch the next instruction from the instruction
    list. If we encounter the [halt] instruction, we return the 
    [haltState], otherwise, we execute the instruction.
*)

Definition step (m : tRMState) : tRMState :=
    match fetch(m) with
    | Halt => haltState m
    | i => execute i m
    end.

Inductive step2 : tRMState ->tRMState -> Prop :=
  | stepRule : forall m, (step2 m (step m)).

(*
  From SfLib
*)

Definition relation (X:Type) := X -> X -> Prop.

Definition deterministic {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2. 

Inductive multi (X:Type) (R: relation X) 
                            : X -> X -> Prop :=
  | multi_refl  : forall (x : X),
                 multi X R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi X R y z ->
                    multi X R x z.
Implicit Arguments multi [[X]].

(*
  SfLib multi ends
*)

(** ** Modeling Program Execution and Non-termination

    The first intuition to define program execution
    as a recursive function fails since [Fixpoint] functions in Coq are
    required to satisfy the property of structural recursion. This does not fit
    with programs containing jumps and loops as these constructs might lead to the 
    possibility of non-termination and hence a predefined number of steps required
    by the structural recursion criterion cannot possibly model this behavior 
    %\cite{Bertot:2008:ICC:1379918.1380269}%.

    The solution to this problem lies in the fact that a program can run 
    indefinitely if it contains infinite loops or mutual jumps and thus should 
    be modeled as an \textbf{infinite trace}. The Coq co-inductive type is 
    the right candidate for this representing such traces.
*)

CoInductive tProgramTrace : Set :=
    | NextRM : tRMState -> tProgramTrace -> tProgramTrace.

(** We now define a CoFixpoint function which generates an infinite trace of run 
    states given an initial machine state.
*)

CoFixpoint generateTrace (rm : tRMState) : tProgramTrace := NextRM rm (generateTrace (step rm)).

Inductive tProgramTrace2 : Type :=
  | starter : tProgramTrace2
  | cont : tRMState -> tProgramTrace2 -> tProgramTrace2.

Inductive validTrace : tRMState -> tProgramTrace2 -> Prop :=
  | triv1 : forall rm, (validTrace rm starter)
  | triv2 : forall rm,(validTrace rm (cont rm starter))
  | nontriv : forall rm rm' rm'' t, (step2 rm' rm'') -> validTrace rm (cont rm' t) -> validTrace rm (cont rm'' (cont rm' t)).

(** The [run] function that starts the machine and uses the lazy [generateTrace] 
    to create a program trace.
*)

Theorem deterministicStep :
  (deterministic step2).
Proof.
  intros rm rm' rm''. generalize dependent rm''.
  generalize dependent rm'.
  induction rm. generalize dependent t. generalize dependent t0. generalize dependent t2. generalize dependent t3.
  destruct t1; intros.
    inversion H. inversion H0. reflexivity.
    inversion H. inversion H0. reflexivity.
  Qed.

Definition halted (rm:tRMState) : Prop :=
  rm = haltState rm.

Theorem progressStep :
  forall rm, (halted rm)\/(exists rm',(step2 rm rm')).
Proof.
  intros. destruct rm.
  destruct t1. right. eapply ex_intro. constructor.
  destruct t1; try right; eapply ex_intro; constructor.
  Qed.

Definition run (m : tRMState) : tProgramTrace:=
    generateTrace m.

(** In order to do meaningful operations on the trace, we define traceHead and 
    traceTail functions on the program trace. These are analogous to the
    well known head and tail functions that operate on lists.
*)

Definition traceHead (x:tProgramTrace) := let (a,s) := x in a.

Definition traceTail (x:tProgramTrace) := let (a,s) := x in s.

(** Using [traceHead] and [traceTail] functions, we define the [nthTrace]
    function that extracts the $n^{th}$ element from a trace and is analogous 
    to the $n^{th}$ function that operate on lists. We declare that the program
    has finished executing if the following condition holds true:
    
    For a program trace P, forall i,
    if nthTrace i P == nthTrace (i+1) P == haltState
    *)

Fixpoint nthTrace (n : nat) (trace: tProgramTrace) : tRMState :=
    match n with
    | O => traceHead trace
    | S n' => nthTrace n' (traceTail trace)
    end.

Fixpoint uptoNTrace (n : nat) (trace: tProgramTrace) : list tRMState :=
    match n with
    | O => (traceHead trace)::nil
    | S n' => (traceHead trace)::(uptoNTrace n' (traceTail trace))
    end.

(** That completes the definition of the register machine. In the following 
    section we run the machine through a set of sample programs. 
    *)

(** ** Sample Run of the Register Machine
    To run the register machine we need a configuration. This configuration is
    defined by the number of value, parameter and return type registers present.
    For our examples, we define a machine with seven registers each for the 
    value, paramter and return types.
*)

Definition regSet : tRegVals :=
    ( 0
    :: 0
    :: 0
    :: 0
    :: 0
    :: 0
    :: 0
    :: nil
    ).

Open Local Scope nat_scope.

(** Our first machine, $\mu$[Machine], is defined as follows:
*)

Definition muMachine : tRMState :=
    ((regSet, regSet, regSet), (nil), (nil), 0, (nil)).

Definition loadMachine (program : tProgram) (machine : tRMState) : tRMState :=
    putProgram program machine.

(** For the purpose of debugging, we define [runSteps]. This function
takes a number of steps through the machine, the number being passed as as 
argument.
*)

Definition runMachine (numSteps : nat) (program : tProgram) (machine : tRMState) : tRMState :=
    nthTrace numSteps (run (loadMachine program machine)).

Definition runMachine2 (numSteps : nat) (program : tProgram) (machine : tRMState) : list tRMState :=
    uptoNTrace numSteps (run (loadMachine program machine)).

Theorem nthEq:
  forall tr n, nthTrace n (traceTail tr) = nthTrace (n + 1) tr.
Proof.
  intros tr n. replace (n + 1) with (S n). simpl. auto.
  omega. Qed.

CoInductive traceEq : tProgramTrace -> tProgramTrace -> Prop :=
  | teq : forall rm rm' t t', rm = rm' -> traceEq t t' -> traceEq (NextRM rm t) (NextRM rm' t').

Inductive stepPres : (list tRMState) -> Prop :=
  | trivP1 : stepPres nil
  | trivP2 : forall rm, stepPres (rm::nil)
  | nontrivP : forall rm rm' rem, step2 rm rm' -> stepPres (rm'::rem) -> stepPres (rm::rm'::rem).

Theorem stepPresTrace :
  forall n rm, stepPres (uptoNTrace n (generateTrace rm)).
Proof.
  induction n. simpl. eapply trivP2.
  simpl. destruct n.
    simpl. intros. eapply nontrivP. apply stepRule. apply trivP2.
    simpl. simpl in IHn. intros. eapply nontrivP. apply stepRule. eapply IHn.
  Qed.

Fixpoint toFiniteTrace (l:list tRMState) (currTrace : tProgramTrace2) : tProgramTrace2 :=
  match l with
  | nil => currTrace
  | rm::remTrace => toFiniteTrace remTrace (cont rm currTrace)
  end.

Theorem validOnlyTrace :
  forall l rm rm' t1, stepPres (rm'::l) -> validTrace rm (cont rm' t1) -> validTrace rm (toFiniteTrace (rm'::l) t1).
Proof.
  intro l.
  induction l. simpl; intros. auto.
  simpl. intros. eapply IHl; inversion H. auto.
  econstructor; auto.
  Qed.

Theorem finite_projection :
  forall n rm p, validTrace (loadMachine p rm) (toFiniteTrace (runMachine2 n p rm) starter).
Proof.
  intro n.
  induction n.
    intros. simpl. eapply triv2.
    simpl. intros. remember (loadMachine p rm) as loadState.
    remember (uptoNTrace n (generateTrace (step loadState))) as trList.
    destruct trList. destruct n; inversion HeqtrList.
    eapply validOnlyTrace. rewrite HeqtrList. eapply stepPresTrace.
    destruct n; simpl in HeqtrList; inversion HeqtrList; constructor; constructor.
  Qed.

(** *** Conditional Jumps, Unconditional Jumps and Arithmetic
    Program A demonstrates basic arithmetic, %\textbf{if-then}% instruction, and 
    the unconditional jump [goto]. 

<<
        00 v0 = 2
        01 v1 = 3
        02 v2 = v0 + v1 // 2 + 3 = 5
        03 v3 = v2 + v1 // 5 + 3 = 8
        04 v4 = v3 * v3 // 8 * 8 = 64
        05 v0 = 64
        06 if v4 == v0 then 11 // true branch will be taken
        07 v2 = 6 
        08 goto 12
        09 Noop
        10 Noop
        11 v2 = 9
        12 Halt
>>
    As a result of running this program register [v2] should contain a 
    value of [9] as the [if] conditional evaluated to true.
*)

Definition programA: tProgram :=
    ( 
(** 00 Entry    *)    (Const (V, 0) 2)
(** 01          *)  ::(Const (V, 1) 3)
(** 02          *)  ::(Add (V, 2) (V, 0) (V, 1))
(** 03          *)  ::(Add (V, 3) (V, 2) (V, 1))
(** 04          *)  ::(Mul (V, 4) (V, 3) (V, 3))
(** 05          *)  ::(Const (V, 0) 64)
(** 06 If v4=v0 *)  ::(If_eq (V, 4) (V, 0) 11)
(** 07          *)  ::(Const (V, 2) 6)
(** 08          *)  ::(Goto 12)
(** 09          *)  ::(Noop)
(** 10          *)  ::(Noop)
(** 11          *)  ::(Const (V, 2) 9)
(** 12 Halt     *)  ::(Halt)
                    ::nil
    ).


(** 
The entire machine is dumped at each step. This lets us verify that the 
program counter is correctly incremented, and allows us to inspect the 
register values at each step of machine execution.
*)

Eval compute in (runMachine 1 programA muMachine).
Eval compute in (runMachine 2 programA muMachine).
Eval compute in (runMachine 3 programA muMachine).
Eval compute in (runMachine 4 programA muMachine).
Eval compute in (runMachine 5 programA muMachine).
Eval compute in (runMachine 6 programA muMachine).
Eval compute in (runMachine 7 programA muMachine).
Eval compute in (runMachine 8 programA muMachine).
Eval compute in (runMachine 9 programA muMachine).

Eval compute in (runMachine 10 programA muMachine).
(** The above commands performs 10 execution steps and 
     yields the following machine state:
<<
     = ((64%Z :: 3%Z :: 9%Z :: 8%Z :: 64%Z :: 0%Z :: 0%Z :: @nil Z,
        0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: @nil Z,
        0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: @nil Z), @nil nat,
       Const (V, 0) 2
       :: Const (V, 1) 3
          :: Add (V, 2) (V, 0) (V, 1)
             :: Add (V, 3) (V, 2) (V, 1)
                :: Mul (V, 4) (V, 3) (V, 3)
                   :: Const (V, 0) 64
                      :: If_eq (V, 4) (V, 0) 11
                         :: Const (V, 2) 6
                            :: Goto 12
                               :: Noop
                                  :: Noop
                                     :: Const (V, 2) 9 :: Halt :: @nil tInstr,
       12, @nil tCallState)
     : tRMState
>>
    As a result of running this program, we have a value of 9 in v2
    Note that the value of PC is 12, which points to the [Halt] instruction. This is
    terminal state of the machine, the [haltState], and by the definition performing 
    further execution will not change the machine state.
    
    Let us illustrate this by running the machine 10,000 times.
*)

Eval compute in (runMachine 10000 programA muMachine).

(** As we had expected, the machine state after 10,000 steps was identical to the first 
    time we encountered the halt instruction:
<<
     = ((64%Z :: 3%Z :: 9%Z :: 8%Z :: 64%Z :: 0%Z :: 0%Z :: @nil Z,
        0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: @nil Z,
        0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: @nil Z), @nil nat,
       Const (V, 0) 2
       :: Const (V, 1) 3
          :: Add (V, 2) (V, 0) (V, 1)
             :: Add (V, 3) (V, 2) (V, 1)
                :: Mul (V, 4) (V, 3) (V, 3)
                   :: Const (V, 0) 64
                      :: If_eq (V, 4) (V, 0) 11
                         :: Const (V, 2) 6
                            :: Goto 12
                               :: Noop
                                  :: Noop
                                     :: Const (V, 2) 9 :: Halt :: @nil tInstr,
       12, @nil tCallState)
     : tRMState
>>
*)

(** *** Function Calls
    In this section we demonstrate the function call mechanism in PVRM.
    In [programB] a function [MyAdd] is defined at instruction [05].
    At instruction [02] [MyAdd] is called with value 2 in [v0] and 3 in [v1].
    The value returned from [MyAdd] is stored in [v2] (instruction 03),
    followed by a jump to the [Halt] instruction at 08.
*)

Definition programB : tProgram :=
    (
(** 00 Entry       *)    (Const (V, 0) 2)
(** 01             *)  ::(Const (V, 1) 3)
(** 02 Call MyAdd  *)  ::(Invoke_static ((V, 0)::(V, 1)::nil) 5)
(** 03             *)  ::(Move_result (V, 2))
(** 04             *)  ::(Goto 8)
(** 05 MyAdd       *)  ::(Add (V, 2) (P, 0) (P, 1))
(** 06             *)  ::(Ret_val (V, 2))
(** 07             *)  ::(Noop)
(** 08 Halt        *)  ::(Halt)
                       ::nil
    ).                   

Eval compute in (runMachine 1 programB muMachine).
Eval compute in (runMachine 2 programB muMachine).
Eval compute in (runMachine 3 programB muMachine).
Eval compute in (runMachine 4 programB muMachine).
Eval compute in (runMachine 5 programB muMachine).
Eval compute in (runMachine 6 programB muMachine).
Eval compute in (runMachine 7 programB muMachine).
Eval compute in (runMachine 8 programB muMachine).
Eval compute in (runMachine 9 programB muMachine).

(** The outcome of running this program is a value of 5 in register [v2] and the
    value of [PC] set to 8.
<<
     = ((2%Z :: 3%Z :: 5%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: @nil Z,
        0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: @nil Z,
        5%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: @nil Z), @nil nat,
       Const (V, 0) 2
       :: Const (V, 1) 3
          :: Invoke_static ((V, 0) :: (V, 1) :: @nil tReg) 5
             :: Move_result (V, 2)
                :: Goto 8
                   :: Add (V, 2) (P, 0) (P, 1)
                      :: Ret_val (V, 2) :: Noop :: Halt :: @nil tInstr, 8,
       @nil tCallState)
     : tRMState
>>

*)

(** *** Recursion
    The next example program demonstrates the use of recursive function calls.
    The register machine code for the factorial program is defined below. This 
    program code is parameterized to accept an argument.
*)

Definition programFact (num : tRegVal) : tProgram :=
    (
(* 00 *)    (Const (V, 2) num)
(*  1 *)    ::(Invoke_static ((V, 2)::nil) 10)
(*  2 *)    ::(Move_result (V, 0))
(*  3 *)    ::(Goto 19)
(*  4 *)    ::(Noop)
(*  5 *)    ::(Noop)
(*  6 *)    ::(Noop)
(*  7 *)    ::(Noop)
(*  8 *)    ::(Noop)
(*  9 *)    ::(Noop)
(* 10 *)    ::(If_gtz (P, 0) 13)
(*  1 *)    ::(Const (V, 0) 1)
(*  2 *)    ::(Ret_val (V, 0))
(*  3 *)    ::(Const (V, 1) (-1))
(*  4 *)    ::(Add (V, 0) (P, 0) (V, 1))
(*  5 *)    ::(Invoke_static ((V, 0)::nil) 10)
(*  6 *)    ::(Move_result (V, 0))
(*  7 *)    ::(Mul (V, 0) (V, 0) (P, 0))
(*  8 *)    ::(Goto 12)
(*  9 *)    ::(Halt)
               ::nil
    ).

Eval compute in (runMachine 100 (programFact 7%Z) muMachine).
Eval compute in (runMachine 100 (programFact 10%Z) muMachine).

Eval compute in (runMachine 1000 (programFact 10%Z) muMachine).

(** The outcome of running the factorial program for 10 leaves a value of 3628800 
    in register [v0] and the value of [PC] set to 19.
<<
     = ((3628800%Z :: 0%Z :: 10%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: nil,
        0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: nil,
        3628800%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: nil), nil,
       Const (V, 2) 10
       :: Invoke_static ((V, 2) :: nil) 10
          :: Move_result (V, 0)
             :: Goto 19
                :: Noop
                   :: Noop
                      :: Noop
                         :: Noop
                            :: Noop
                               :: Noop
                                  :: If_gtz (P, 0) 13
                                     :: Const (V, 0) 1
                                        :: Ret_val (V, 0)
                                           :: Const (V, 1) (-1)
                                              :: Add (V, 0) (P, 0) (V, 1)
                                                 :: Invoke_static
                                                      ((V, 0) :: nil) 10
                                                    :: Move_result (V, 0)
                                                       :: Mul (V, 0) 
                                                            (V, 0) (P, 0)
                                                          :: Goto 12
                                                             :: Halt :: nil,
       19, nil)
     : tRMState
>>

*)

Close Local Scope nat_scope.
    
Close Scope Z_scope.

End RMImpl.

(** Finally, we extract this machine to a Haskell implementation. The extracted
implementation is then packaged into an executable. 
*)