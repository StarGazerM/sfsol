Add LoadPath "D:\sfsol".
Require Export SfLib.
Require Import String.

Definition ProgramCounter : Type := nat.

Definition clist (X : Type) := list (ProgramCounter * X).

Inductive StringIndex : Type :=
  | strAt : string -> nat -> StringIndex.

Inductive Constant : Type :=
  | cnat : nat -> Constant
  | cstr : StringIndex -> Constant
  | ctrue : Constant
  | cfalse : Constant
  | cnull : Constant.

Inductive UnaryOperator : Type :=
  | unot : UnaryOperator.

Inductive BinaryArithOperator : Type :=
  | badd : BinaryArithOperator
  | bsub : BinaryArithOperator
  | bmult : BinaryArithOperator
  | bdiv : BinaryArithOperator
  | bmod : BinaryArithOperator
  | band : BinaryArithOperator
  | bor : BinaryArithOperator
  | bxor : BinaryArithOperator.

Inductive BinaryCompOperator : Type :=
  | beq : BinaryCompOperator
  | blt : BinaryCompOperator
  | bgt : BinaryCompOperator.

Definition RegIndex := nat.

Inductive Register : Type :=
  | Reg : RegIndex -> Register.

Definition Regs := list Register.

Definition Addr := nat.

Definition Addrs := list Addr.

Inductive PrimType : Type :=
  | boolean : bool -> PrimType
  | char : nat -> PrimType
  | int : nat -> PrimType.

Inductive pTypes : Type :=
  | bT : pTypes
  | cT : pTypes
  | iT : pTypes.

Inductive Class : Type :=
  | top : Class
  | class : StringIndex -> ClassIndex -> list FieldIndex -> list MethodIndex -> Class
with ClassIndex : Type :=
  | classAt : Class -> nat -> ClassIndex
with Field : Type :=
  | field : StringIndex -> ClassIndex -> Field
with FieldIndex : Type :=
  | fieldAt : Field -> nat -> FieldIndex
with Method : Type :=
  | method : StringIndex -> ClassIndex -> list TypeIndex -> TypeIndex -> nat -> clist Instruction -> Method
with MethodIndex : Type :=
  | methodAt : Method -> nat -> MethodIndex
with Instruction : Type :=
  | nop : Instruction
  | ret : Instruction
  | retTo : Register -> Instruction
  | invoke : list rhs -> MethodIndex -> Instruction
  | goto : ProgramCounter -> Instruction
  | branch : Register -> BinaryCompOperator -> Register -> ProgramCounter -> Instruction
  | move : lhs -> rhs -> Instruction
  | unaryArith : Register -> UnaryOperator -> Register -> Instruction
  | binaryArith : Register -> Register -> BinaryArithOperator -> Register -> Instruction
  | new : Register -> ClassIndex -> Instruction
  | newarr : Register -> DalType -> Register -> Instruction
  | cast : Register -> DalType -> Register -> Instruction
with lhs : Type :=
  | reg : Register -> lhs
  | acc : Register -> Register -> lhs
  | ifield : Register -> FieldIndex -> lhs
  | sfield : FieldIndex -> lhs
with rhs : Type :=
  | l : lhs -> rhs
  | c : Constant -> rhs
with DalType : Type :=
  | refT : RefType -> DalType
  | primT : pTypes -> DalType
with TypeIndex : Type :=
  | typeAt : DalType -> nat -> TypeIndex
with RefType : Type :=
  | cls : Class -> RefType
  | arrRef : RefType -> nat -> RefType
  | arrPrim : PrimType -> nat -> RefType
with Ref : Type :=
  | lRef : Location -> Ref
  | null : Ref
with Val : Type :=
  | prim : PrimType -> Val
  | ref : Ref -> Val
  | siv : StringIndex -> Val
with Object : Type :=
  | topObj : Object
  | obj : ClassIndex -> list (FieldIndex * Val) -> Object
with Array : Type :=
  | arr : nat -> list Val -> Array
with arrOrObj : Type :=
  | ar : Array -> arrOrObj
  | ob : Object -> arrOrObj
with Location : Type :=
  | locIn : nat -> Location.

Definition RegVal := Val.

Definition RegVals := list RegVal.

Definition RegState : Type := RegVals.

Definition PCVal := nat.

Definition Program := list ClassIndex.

(* Operator Arithmetic *)

Definition top1: Class := top.

Definition top2: Class := top.

Inductive Option {X : Type} : Type :=
  | None : Option
  | Some : X -> Option.

Fixpoint nth {A:Type} (n:nat) (l:list A) : (@Option A) :=
  match l,n with
  | [],_ => None
  | cons x lst,0 => Some x
  | cons x lst,(S n') => nth n' lst
  end.

Definition areSameSI (si1 si2:StringIndex) : bool :=
  match si1,si2 with
  | (strAt s1 n1),(strAt s2 n2) => (beq_nat n1 n2)
  end.

Fixpoint isSubClass (c1 c2:Class) : bool :=
  match c1,c2 with
  | _,top => true
  | top,_ => false
  | (class si1 ci1 fi1 mi1),(class si2 ci2 fi2 mi2)=> match (areSameSI si1 si2) with
    | true => true
    | false => match ci1 with
      | (classAt c1' n) => isSubClass c1' (class si2 ci2 fi2 mi2)
      end
    end
  end.

Definition areSameClass (c1 c2:Class) : bool :=
  (andb (isSubClass c1 c2) (isSubClass c2 c1)).

Fixpoint arePrim (n1:DalType) (n2:DalType) : (@Option bool) :=
  match n1 with
  | (refT x) => None
  | (primT x) => match n2 with
    | (refT y) => None
    | (primT y) => (Some true)
    end
  end.

Fixpoint areEqualNum (n1:nat) (n2:nat) : bool :=
  match n1 with
  | O => match n2 with
    | O => true
    | _ => false
    end
  | (S n1') => match n2 with
    | O => false
    | (S n2') => (areEqualNum n1' n2')
    end
  end.

Definition areSameCI (ci1 ci2:ClassIndex) : bool :=
  match ci1,ci2 with
  | (classAt c1 n1),(classAt c2 n2) => andb (areSameClass c1 c2) (areEqualNum n1 n2)
  end.

Fixpoint areEqualBool (b1 b2:bool) : bool :=
  match b1 , b2 with
  | true,true => true
  | false,false => true
  | _,_ => false
  end.

Fixpoint isle_num (m n:nat) : bool :=
  match m with
  | O => true
  | (S m') => match n with
    | O => false
    | (S n') => (isle_num m' n')
    end
  end.

Fixpoint div (m n:nat) {struct m} : nat :=
  match m with
  | O => O
  | (S m') => match (areEqualNum n (m - (mult (div m' n) n))) with
    | true => S (div m' n)
    | false => (div m' n)
    end
  end.

Compute (div 3 0).

Definition mod (m n:nat) : nat := m - (mult (div m n) n).

Compute (mod 3 2).

Fixpoint areEqualPrim (b1 b2:PrimType): (@Option bool) :=
  match b1,b2 with
  | boolean x,boolean y => Some (areEqualBool x y)
  | char x,char y => Some (areEqualNum x y)
  | int x,int y => Some (areEqualNum x y)
  | _,_ => None
  end.

Definition castIntToChar (n: nat) : nat := (mod n 128).

Definition castBoolToCharOrInt (b: bool) : nat :=
  match b with
  | true => 1
  | false => 0
  end.

Definition castCharOrIntToBool (n:nat) : bool :=
  (negb (areEqualNum n 0)).

Definition castToChar (x:PrimType) : nat :=
  match x with
  | char x' => x'
  | int x' => (castIntToChar x')
  | boolean x' => (castBoolToCharOrInt x')
  end.

Definition castToInt (x:PrimType) : nat :=
  match x with
  | char x' => x'
  | int x' => x'
  | boolean x' => (castBoolToCharOrInt x')
  end.

Definition castToBool (x:PrimType) : bool :=
  match x with
  | char x' => (castCharOrIntToBool x')
  | int x' => (castCharOrIntToBool x')
  | boolean x' => x'
  end.

Definition addPrims (n1 n2: PrimType) : (@Option PrimType) :=
  Some (int (plus (castToInt n1) (castToInt n2))).

Definition subPrims (n1 n2: PrimType) : (@Option PrimType) :=
  Some (int (minus (castToInt n1) (castToInt n2))).

Definition multPrims (n1 n2: PrimType) : (@Option PrimType) :=
  Some (int (mult (castToInt n1) (castToInt n2))).

Definition divPrims (n1 n2: PrimType) : (@Option PrimType) :=
  Some (int (div (castToInt n1) (castToInt n2))).

Definition modPrims (n1 n2: PrimType) : (@Option PrimType) :=
  Some (int (mod (castToInt n1) (castToInt n2))).

Definition andPrims (n1 n2: PrimType) : (@Option PrimType) :=
  Some (boolean (andb (castToBool n1) (castToBool n2))).

Definition orPrims (n1 n2: PrimType) : (@Option PrimType) :=
  Some (boolean (orb (castToBool n1) (castToBool n2))).

Definition xorPrims (n1 n2: PrimType) : (@Option PrimType) :=
  Some (boolean (xorb (castToBool n1) (castToBool n2))).

Definition eqPrims (n1 n2: PrimType) : (@Option PrimType) :=
  Some (boolean (negb (xorb (castToBool n1) (castToBool n2)))).

Definition ltPrims (n1 n2: PrimType) : (@Option PrimType) :=
  Some (boolean (isle_num ((castToInt n1) + 1) (castToInt n2))).

Definition gtPrims (n1 n2: PrimType) : (@Option PrimType) :=
  Some (boolean (isle_num ((castToInt n2) + 1) (castToInt n1))).

Definition notPrims (n1: PrimType) : (@Option PrimType) :=
  Some (boolean (negb (castToBool n1))).

Definition applyBinArOp (bop: BinaryArithOperator) (n1 n2: PrimType) : (@Option PrimType) :=
  match bop with
  | badd => (addPrims n1 n2)
  | bsub => (subPrims n1 n2)
  | bmult => (multPrims n1 n2)
  | bdiv => (divPrims n1 n2)
  | bmod => (modPrims n1 n2)
  | band => (andPrims n1 n2)
  | bor => (orPrims n1 n2)
  | bxor => (xorPrims n1 n2)
  end.

Definition applyBinCmpOp (bop: BinaryCompOperator) (n1 n2: PrimType) : (@Option PrimType) :=
  match bop with
  | beq => (eqPrims n1 n2)
  | blt => (ltPrims n1 n2)
  | bgt => (gtPrims n1 n2)
  end.

Definition applyUnOp (uop: UnaryOperator) (n1: PrimType) : (@Option PrimType) :=
  match uop with
  | unot => (notPrims n1)
  end.

Fixpoint getInstAtInsts (pc:ProgramCounter) (insts:clist Instruction) : (@Option Instruction) :=
  match insts with
  | [] => None
  | (n,ins)::xs => match (areEqualNum n pc) with
    | true => Some ins
    | false => (getInstAtInsts pc xs)
    end
  end.

Fixpoint getInstAtMIs (pc:ProgramCounter) (mis:list MethodIndex) : (@Option Instruction) :=
  match mis with
  | [] => None
  | (methodAt (method si ci tis ti n insts) _)::xs => 
    match (getInstAtInsts pc insts) with
    | None => (getInstAtMIs pc xs)
    | x => x
    end
  end.

Fixpoint getInstAt (pc:ProgramCounter) (p:Program) : (@Option Instruction) :=
  match p with
  | [] => None
  | (classAt top _)::xs => None
  | (classAt (class si ci fi mis) _)::xs =>
    match (getInstAtMIs pc mis) with
    | None => (getInstAt pc xs)
    | x => x
    end
  end.

Fixpoint getFirstPCMethod (mi:MethodIndex) : (@Option ProgramCounter) :=
  match mi with
  | (methodAt (method si ci tis ti n insts) _) =>
    match insts with
    | [] => None
    | (x,y)::rem => Some x
    end
  end.

Definition LocalReg : Type := (list (Register*Val)).

Inductive Frame : Type := 
  | frm : (MethodIndex * ProgramCounter * LocalReg) -> Frame.

Inductive ExcFrame : Type :=
  | exc : Location * MethodIndex * ProgramCounter -> ExcFrame.

Inductive callStack : Type :=
  | cf : Frame * list Frame -> callStack
  | ce : ExcFrame * list Frame -> callStack.

Inductive ValOrRef : Type :=
  | v : Val -> ValOrRef
  | a : arrOrObj -> ValOrRef.

Definition StaticHeap : Type := list (FieldIndex * ValOrRef).

Definition Heap : Type := list arrOrObj.

Inductive Config : Type := 
  | cnf : StaticHeap * Heap * callStack -> Config.

Fixpoint getPCconfig (init:Config) : ProgramCounter :=
  match init with
  | cnf (sh,h,(ce (exc (lc,mi,pc),lst))) => pc
  | cnf (sh,h,(cf (frm (mi,pc,lrg),lst))) => pc
  end.

Fixpoint updatePCconfig (init:Config) (pc:ProgramCounter) : Config :=
  match init with
  | cnf (sh,h,(ce (exc (lc,mi,pc'),lst))) => cnf (sh,h,(ce (exc (lc,mi,pc),lst)))
  | cnf (sh,h,(cf (frm (mi,pc',lrg),lst))) => cnf (sh,h,(cf (frm (mi,pc,lrg),lst)))
  end.

Definition updateLocalReg (r:Register) (v:Val) (lr:LocalReg): LocalReg := (r,v)::lr.

Fixpoint findInLocalReg (r:Register) (lr:LocalReg): (@Option Val) :=
  match lr with
  | [] => None
  | (x,y)::rem => match (x,r) with
    | ((Reg n1),(Reg n2)) => match (areEqualNum n1 n2) with
      | true => Some y
      | false => (findInLocalReg r rem)
      end
    end
  end.

Fixpoint regToValLocalRegs (r:Register) (lr:LocalReg) : (@Option Val) :=
  match lr with
  | nil => None
  | cons (r',val) rem => match (r,r') with
    | (Reg ri,Reg ri') => match (areEqualNum ri ri') with
      | true => Some val
      | false => (regToValLocalRegs r rem)
      end
    end
  end.

Fixpoint regToValFrame (r:Register) (f:Frame) : (@Option Val) :=
  match f with
  | frm (mi,pc,lr) => regToValLocalRegs r lr
  end.

Fixpoint regToValFrames (r:Register) (fL:list Frame) : (@Option Val) :=
  match fL with
  | nil => None
  | cons f rem =>  match (regToValFrame r f) with
    | None => (regToValFrames r rem)
    | x => x
    end
  end.

Fixpoint regToVal (r:Register) (conf:Config) : (@Option Val) :=
  match conf with
  | cnf (sh,h,(ce (eF,lst))) => (regToValFrames r lst)
  | cnf (sh,h,(cf (fm,lst))) => match (regToValFrame r fm) with
    | None => (regToValFrames r lst)
    | x => x
    end
  end.

Fixpoint refToVal (rf:Ref) (conf:Config) : (@Option arrOrObj) :=
  match rf,conf with
  | (lRef (locIn n)),(cnf (sh,h,cs)) => (nth n h)
  | _,_ => None
  end.

Fixpoint accToVal (r1 r2:Register) (conf:Config) : (@Option Val) :=
  match (regToVal r1 conf),(regToVal r2 conf) with
  | None,_ => None
  | Some (ref rf),Some (prim x) => match (refToVal rf conf) with
    | Some (ar (arr n vals)) => (nth (castToInt x) vals)
    | _ => None
    end
  | _,_ => None
  end.

Fixpoint areSameFI (fi1 fi2:FieldIndex) : bool :=
  match fi1,fi2 with
  | (fieldAt (field SI1 CI1) n1),(fieldAt (field SI2 CI2) n2) => andb (andb (areSameSI SI1 SI2) (areSameCI CI1 CI2)) (areEqualNum n1 n2)
  end.

Fixpoint findFI {X:Type} (fi:FieldIndex) (l:list (FieldIndex * X)) : (@Option X) :=
  match l with
  | nil => None
  | cons (fi',val) rem => match (areSameFI fi fi') with
    | true => Some val
    | false => findFI fi rem
    end
  end.

Fixpoint ifieldToVal (r1:Register) (fi:FieldIndex) (conf:Config) : (@Option Val) :=
  match (regToVal r1 conf) with
  | Some (ref rf) => match (refToVal rf conf) with
    | Some (ob (obj ci flst)) => (findFI fi flst)
    | _ => None
    end
  | _ => None
  end.

Fixpoint sfieldToVal (fi:FieldIndex) (conf:Config) : (@Option ValOrRef) :=
  match conf with
  | (cnf (sh,h,cs)) => (findFI fi sh)
  end.

Fixpoint ValToValOrRef (val:@Option Val) : (@Option ValOrRef) :=
  match val with
  | Some x => Some (v x)
  | None => None
  end.

Fixpoint ValOrRefToVal (val:@Option ValOrRef) : (@Option Val) :=
  match val with
  | Some (v x) => Some x
  | _ => None
  end.

Definition lhsToVal (l:lhs) (conf:Config) : (@Option ValOrRef):=
  match l with
  | (reg r) => ValToValOrRef (regToVal r conf)
  | (acc r1 r2) => ValToValOrRef (accToVal r1 r2 conf)
  | (ifield r1 fi) => ValToValOrRef (ifieldToVal r1 fi conf)
  | (sfield fi) => sfieldToVal fi conf
  end.

Definition lhsToReg (l:lhs) (r:Register) (conf:Config) : (@Option (Register*ValOrRef)) :=
  match (lhsToVal l conf) with
  | Some x => Some (r,x)
  | None => None
  end.

Definition constantToVal (c:Constant) : (@Option ValOrRef) :=
  match c with
  | cnat n => Some (v (prim (int n)))
  | cstr s => Some (v (siv s))
  | ctrue => Some (v (prim (boolean true)))
  | cfalse => Some (v (prim (boolean false)))
  | cnull => Some (v (ref null))
  end.

Fixpoint rhsToVal (r:rhs) (conf:Config) : (@Option ValOrRef) :=
  match r with
  | l ls => (lhsToVal ls conf)
  | c cnst => (constantToVal cnst)
  end.

Definition rhsToReg (r:rhs) (r1:Register) (conf:Config) : (@Option (Register*ValOrRef)) :=
  match (rhsToVal r conf) with
  | Some x => Some (r1,x)
  | None => None
  end.

Fixpoint setInLocalReg (r:Register) (lr:LocalReg) (vl:@Option Val) : (@Option LocalReg) :=
  match vl,lr with
  | None,_ => None
  | Some vl,[] => None
  | Some vl,cons (r',v') rem => match r,r' with
    | Reg n,Reg n' => match (areEqualNum n n') with
      | true => Some (cons (r',vl) rem)
      | false => match (setInLocalReg r rem (Some vl)) with
        | Some lr' => Some (cons (r',v') lr')
        | None => None
        end
      end
    end
  end.

Fixpoint valToRegFrame (r:Register) (f:Frame) (vl:@Option Val) : (@Option Frame) :=
  match f with
  | frm (mi,pc,lr) => match (setInLocalReg r lr vl) with
    | Some lr' => Some (frm (mi,pc,lr'))
    | _ => None
    end
  end.

Fixpoint valToRegFrames (r:Register) (fL:list Frame) (vl:@Option Val) : @Option (list Frame) :=
  match fL,vl with
  | _,None => None
  | nil,Some vl => None
  | cons f rem,Some vl =>  match (valToRegFrame r f (Some vl)) with
    | Some f' => Some (cons f' rem)
    | None => match (valToRegFrames r rem (Some vl)) with
      | Some rem' => Some (cons f rem')
      | None => None
      end
    end
  end.

Fixpoint valToReg (r:Register) (conf:Config) (vl:@Option Val) : (@Option Config) :=
  match conf with
  | cnf (sh,h,(ce (eF,lst))) => match (valToRegFrames r lst vl) with
    | Some lst' => Some (cnf (sh,h,(ce (eF,lst))))
    | None => None
    end
  | cnf (sh,h,(cf (fm,lst))) => match (valToRegFrame r fm vl) with
    | Some fm' => Some (cnf (sh,h,(cf (fm',lst))))
    | None => match (valToRegFrames r lst vl) with
      | Some lst' => Some (cnf (sh,h,(cf (fm,lst'))))
      | None => None
      end
    end
  end.

Fixpoint setNth {X:Type} (x:X) (n:nat) (l:list X) : (@Option (list X)) :=
  match l,n with
  | [],_ => None
  | (cons x' rem),0 => Some (cons x rem)
  | (cons x' rem),S n' => match (setNth x n' rem) with
    | None => None
    | Some rem' => Some (cons x' rem')
    end
  end.

Fixpoint setAtRef (rf:Ref) (conf:Config) (vl:@Option arrOrObj) : (@Option Config) :=
  match rf,conf,vl with
  | (lRef (locIn n)),(cnf (sh,h,cs)),Some vl => match (setNth vl n h) with
    | Some h' => Some (cnf (sh,h',cs))
    | _ => None
    end
  | _,_,_ => None
  end.

Fixpoint valToAcc (r1 r2:Register) (conf:Config) (vl:@Option Val) : (@Option Config) :=
  match (regToVal r1 conf),(regToVal r2 conf),vl with
  | None,_,_ => None
  | Some (ref rf),Some (prim x),Some vl => match (refToVal rf conf) with
    | Some (ar (arr n vals)) => match (setNth vl (castToInt x) vals) with
      | None => None
      | Some vals' => (setAtRef rf conf (Some (ar (arr n vals'))))
      end
    | _ => None
    end
  | _,_,_ => None
  end.

Fixpoint setAtFI {X:Type} (x:X) (fi:FieldIndex) (l:list (FieldIndex * X)) : (@Option (list (FieldIndex * X))) :=
  match l with
  | nil => None
  | cons (fi',x') rem => match (areSameFI fi fi') with
    | true => Some (cons (fi',x) rem)
    | false => match (setAtFI x fi rem) with
      | Some rem' => Some (cons (fi',x') rem')
      | _ => None
      end
    end
  end.

Fixpoint valToIfield (r1:Register) (fi:FieldIndex) (conf:Config) (vl:@Option Val) : (@Option Config) :=
  match (regToVal r1 conf) with
  | Some (ref rf) => match (refToVal rf conf),vl with
    | Some (ob (obj ci flst)),Some vl => match (setAtFI vl fi flst) with
      | Some flst' => (setAtRef rf conf (Some (ob (obj ci flst'))))
      | _ => None
      end
    | _,_ => None
    end
  | _ => None
  end.

Fixpoint valToSfield (fi:FieldIndex) (conf:Config) (vl:@Option ValOrRef) : (@Option Config) :=
  match conf,vl with
  | (cnf (sh,h,cs)),Some vl => match (setAtFI vl fi sh) with
    | Some sh' => Some (cnf (sh',h,cs))
    | _ => None
    end
  | _,_ => None
  end.

Definition newPrim (pt:pTypes) : PrimType :=
  match pt with
  | bT => (boolean false)
  | cT => (char 0)
  | iT => (int 0)
  end.

Fixpoint createList {X:Type} (n:nat) (x:X) : list X :=
  match n with
  | 0 => nil
  | S n' => cons x (createList n' x)
  end.

Definition newArrPrim (n:nat) (pt:pTypes) : Array :=
  arr n (createList n (prim (newPrim pt))).

Fixpoint newObject (c:Class) : Object :=
  match c with
  | top => topObject
  | (class SI CI FIs MIs) => 

with newInstance (t:DalType) : (ValOrRef) :=
  match ti with
  | (primT pt) => (v (prim (newPrim pt)))
  | (refT (cls c)) => (a (ob (newObject c)))
  | (refT (arrRef rt)) => (a (ar (newArrRef rt)))
  | (refT (arrPrim pt)) => (v ())

Fixpoint step (init:Config) (p:Program): (@Option Config) :=
  match (getInstAt (getPCconfig init) p) with
  | None => None
  | Some x => match x with
    | nop => Some (updatePCconfig init ((getPCconfig init)+1))
    | (goto pc) => Some (updatePCconfig init pc)
    | (invoke args m) =>
    | x => None
    end
  end.