

From Coq
    Require Import ZArith.ZArith Strings.String.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype tuple zmodp.

Definition BITS n := n.-tuple bool.

Definition n3 := 3.
Definition n7 := 7.
Definition n15 := 15.
Definition n31 := 31.
Definition n63 := 63.
Arguments n3 : simpl never.
Arguments n7 : simpl never.
Arguments n15 : simpl never.
Arguments n31 : simpl never.
Arguments n63 : simpl never.
Opaque n3 n7 n15 n31 n63.
Notation n4 := n3.+1.
Notation n8 := n7.+1.
Notation n16 := n15.+1.
Notation n32 := n31.+1.
Notation n64 := n63.+1.
Definition n24 := 24.
Arguments n24 : simpl never.
Opaque n24.
Definition NIBBLE := BITS n4.

Inductive OpSize := OpSize1 | OpSize2 | OpSize4 | OpSize8.

Definition opSizeToNat s :=
  match s with OpSize1 => 1 | OpSize2 => 2 | OpSize4 => 4 | OpSize8 => 8 end.

Definition VWORD s :=
  BITS (match s with OpSize1 => n8 | OpSize2 => n16 | OpSize4 => n32 | OpSize8 => n64 end).
Definition BYTE   := (VWORD OpSize1).
Definition WORD   := (VWORD OpSize2).
Definition DWORD  := (VWORD OpSize4).
Definition QWORD  := (VWORD OpSize8).


Identity Coercion VWORDtoBITS : VWORD >-> BITS.
Identity Coercion BYTEtoVWORD : BYTE >-> VWORD.
Identity Coercion WORDtoVWORD : WORD >-> VWORD.
Identity Coercion DWORDtoVWORD : DWORD >-> VWORD.
Identity Coercion QWORDtoVWORD : QWORD >-> VWORD.

Notation "'nilB'" := (nil_tuple _).
Definition consB {n} (b:bool) (p: BITS n) : BITS n.+1 := cons_tuple b p.
Definition joinlsb {n} (pair: BITS n*bool) : BITS n.+1 := cons_tuple pair.2 pair.1.

Definition splitlsb {n} (p: BITS n.+1): BITS n*bool := (behead_tuple p, thead p).
Definition droplsb {n} (p: BITS n.+1) := (splitlsb p).1.

Fixpoint fromNat {n} m : BITS n :=
  if n is _.+1
  then joinlsb (fromNat m./2, odd m)
  else nilB.
Notation "# m" := (fromNat m) (at level 0).
Arguments fromNat n m : simpl never.

Definition toNat {n} (p: BITS n) := foldr (fun (b:bool) n => b + n.*2) 0 p.

Coercion natAsQWORD := @fromNat _ : nat -> QWORD.
Coercion natAsDWORD := @fromNat _ : nat -> DWORD.
Coercion natAsWORD := @fromNat _ : nat -> WORD.
Coercion natAsBYTE := @fromNat _ : nat -> BYTE.

Definition copy n b : BITS n := nseq_tuple n b.
Definition zero n := copy n false.
Definition ones n := copy n true.

Definition msb {n} (b: BITS n) := last false b.
Definition lsb {n} (b: BITS n) := head false b.

Definition catB {n1 n2} (p1: BITS n1) (p2: BITS n2) : BITS (n2+n1) :=
  cat_tuple p2 p1.
Notation "y ## x" := (catB y x) (right associativity, at level 60).

Fixpoint high n {n2} : BITS (n2+n) -> BITS n :=
  if n2 is _.+1 then fun p => let (p,b) := splitlsb p in high _ p else fun p => p.

Fixpoint low {n1} n : BITS (n+n1) -> BITS n :=
  if n is _.+1 then fun p => let (p,b) := splitlsb p in joinlsb (low _ p, b)
               else fun p => nilB.

Definition split2 n1 n2 p := (high n1 p, low n2 p).

Definition split3 n1 n2 n3 (p: BITS (n3+n2+n1)) : BITS n1 * BITS n2 * BITS n3 :=
  let (hi,lo) := split2 n1 _ p in
  let (lohi,lolo) := split2 n2 _ lo in (hi,lohi,lolo).

Definition split4 n1 n2 n3 n4 (p: BITS (n4+n3+n2+n1)): BITS n1 * BITS n2 * BITS n3 * BITS n4 :=
  let (b1,rest) := split2 n1 _ p in
  let (b2,rest) := split2 n2 _ rest in
  let (b3,b4)   := split2 n3 _ rest in (b1,b2,b3,b4).

Definition signExtend extra {n} (p: BITS n.+1) := copy extra (msb p) ## p.

Definition signTruncate extra {n} (p: BITS (n.+1 + extra)) : option (BITS n.+1) :=
  let (hi,lo) := split2 extra _ p in
  if msb lo && (hi == ones _) || negb (msb lo) && (hi == zero _)
  then Some lo
  else None.

Definition zeroExtend extra {n} (p: BITS n) := zero extra ## p.
Fixpoint lowWithZeroExtend m {n} : BITS n -> BITS m :=
  if n is _.+1
  then fun p => let (p,b) := splitlsb p in
                if m is m'.+1 then joinlsb (@lowWithZeroExtend m' _ p, b)
                else zero 0
  else fun p => zero m.

Definition zeroTruncate extra {n} (p: BITS (n + extra)) : option (BITS n) :=
  let (hi,lo) := split2 extra _ p in
  if hi == zero _ then Some lo else None.

Fixpoint splitmsb {n} : BITS n.+1 -> bool * BITS n :=
  if n is _.+1
  then fun p => let (p,b) := splitlsb p in let (c,r) := splitmsb p in (c,joinlsb(r,b))
  else fun p => let (p,b) := splitlsb p in (b,p).
Definition dropmsb {n} (p: BITS n.+1) := (splitmsb p).2.

Fixpoint joinmsb {n} : bool * BITS n -> BITS n.+1 :=
  if n is _.+1
  then fun p => let (hibit, p) := p in
                let (p,b) := splitlsb p in joinlsb (joinmsb (hibit, p), b)
  else fun p => joinlsb (nilB, p.1).
Definition joinmsb0 {n} (p: BITS n) : BITS n.+1 := joinmsb (false,p).

Fixpoint zeroExtendAux extra {n} (p: BITS n) : BITS (extra+n) :=
  if extra is e.+1 then joinmsb0 (zeroExtendAux e p) else p.

Definition joinNibble {n}  (p:NIBBLE) (q: BITS n) : BITS (n.+4) :=
  let (p1,b0) := splitlsb p in
  let (p2,b1) := splitlsb p1 in
  let (p3,b2) := splitlsb p2 in
  let (p4,b3) := splitlsb p3 in
   joinmsb (b3, joinmsb (b2, joinmsb (b1, joinmsb (b0, q)))).

Notation "y ## x" := (catB y x) (right associativity, at level 60).

Definition slice n n1 n2 (p: BITS (n+n1+n2)) : BITS n1 :=
  let: (a,b,c) := split3 n2 n1 n p in b.

Definition updateSlice n n1 n2 (p: BITS (n+n1+n2)) (m:BITS n1) : BITS (n+n1+n2) :=
  let: (a,b,c) := split3 n2 n1 n p in a ## m ## c.

Fixpoint seqBytesToBits (xs : seq BYTE) : BITS (size xs*8) :=
  if xs is x::xs' return BITS (size xs*8) then seqBytesToBits xs' ## x
  else nilB.

Fixpoint bytesToBits {n} : (n.-tuple BYTE) -> BITS (n*8) :=
  if n is n'.+1 return n.-tuple BYTE -> BITS (n*8)
  then fun xs => bytesToBits (behead_tuple xs) ## (thead xs)
  else fun xs => nilB.

Definition splitAtByte n (bits : BITS ((n.+1)*8)) :BITS (n*8) * BYTE := (split2 (n*8) 8 bits).

Fixpoint bitsToBytes n : BITS (n*8) -> n.-tuple BYTE :=
  if n is n'.+1 return BITS (n*8) -> n.-tuple BYTE
  then fun xs =>
    let (hi,lo) := splitAtByte n' xs in cons_tuple lo (bitsToBytes _ hi)
  else fun xs => nil_tuple _.

Coercion singleBit b : BITS 1 := joinlsb (nilB, b).

Definition getBit {n} (p: BITS n) (i:nat) := nth false p i.

Fixpoint setBitAux {n} i b : BITS n -> BITS n :=
  if n is _.+1
  then fun p => let (p,oldb) := splitlsb p in
                if i is i'.+1 then joinlsb (setBitAux i' b p, oldb) else joinlsb (p,b)
  else fun p => nilB.

Definition setBit {n} (p: BITS n) i b := setBitAux i b p.

Definition toPosZ {n} (p: BITS n) :=
  foldr (fun b z => if b then Z.succ (Z.double z) else Z.double z) Z0 p.

Definition toNegZ {n} (p: BITS n) :=
  foldr (fun b z => if b then Z.double z else Z.succ (Z.double z)) Z0 p.

Definition toZ {n} (bs: BITS n.+1) :=
  match splitmsb bs with
  | (false, bs') => toPosZ bs'
  | (true, bs') => Z.opp (Z.succ (toNegZ bs'))
  end.

Fixpoint fromPosZ {n} (z: Z): BITS n :=
  if n is _.+1
  then joinlsb (fromPosZ (Z.div2 z), negb (Zeven_bool z))
  else nilB.

Fixpoint fromNegZ {n} (z: Z): BITS n :=
  if n is _.+1
  then joinlsb (fromNegZ (Z.div2 z), Zeven_bool z)
  else nilB.

Definition fromZ {n} (z:Z) : BITS n :=
  match z with
  | Zpos _ => fromPosZ z
  | Zneg _ => fromNegZ (Z.pred (Z.opp z))
  | _ => zero _
  end.

Definition toZp {n} (p: BITS n) : 'Z_(2^n) := inZp (toNat p).
Definition fromZp {n} (z: 'Z_(2^n)) : BITS n := fromNat z.

Definition bool_inZp m (b:bool): 'Z_m := inZp b.
Definition toZpAux {m n} (p:BITS n) : 'Z_(2^m) := inZp (toNat p).


Section HexStrings.
Import Ascii.

Definition charToNibble c : NIBBLE :=
  fromNat (findex 0 (String c EmptyString) "0123456789ABCDEF0123456789abcdef").
Definition charToBit c : bool := ascii_dec c "1".

Fixpoint fromBin s : BITS (length s) :=
  if s is String c s
  then joinmsb (charToBit c, fromBin s) else #0.
Fixpoint fromHex s : BITS (length s * 4) :=
  if s is String c s
  then joinNibble (charToNibble c) (fromHex s) else #0.
Fixpoint fromString s : BITS (length s * 8) :=
  if s is String c s return BITS (length s * 8)
  then fromString s ## fromNat (n:=8) (nat_of_ascii c) else nilB.

Definition nibbleToChar (n: NIBBLE) :=
  match String.get (toNat n) "0123456789ABCDEF" with None => " "%char | Some c => c end.

Definition appendNibbleOnString n s :=
  (s ++ String.String (nibbleToChar n) EmptyString)%string.

End HexStrings.

Fixpoint toHex {n} :=
  match n return BITS n -> string with
  | 0 => fun bs => EmptyString
  | 1 => fun bs => appendNibbleOnString (zero 3 ## bs) EmptyString
  | 2 => fun bs => appendNibbleOnString (zero 2 ## bs) EmptyString
  | 3 => fun bs => appendNibbleOnString (zero 1 ## bs) EmptyString
  | _ => fun bs => let (hi,lo) := split2 _ 4 bs in appendNibbleOnString lo (toHex hi)
  end.

Import Ascii.
Fixpoint bytesToHexAux (b: seq BYTE) res :=
  match b with b::bs =>
    bytesToHexAux bs (String.String (nibbleToChar (high (n2:=4) 4 b)) (
             String.String (nibbleToChar (low 4 b)) (
             String.String (" "%char) res)))
  | nil => res end.

Definition bytesToHex b := bytesToHexAux (rev b) ""%string.

Definition charToBYTE (c: ascii) : BYTE :=
  let (a0,a1,a2,a3,a4,a5,a6,a7) := c in
  [tuple a0;a1;a2;a3;a4;a5;a6;a7].

Fixpoint stringToTupleBYTE (s: string) : (length s).-tuple BYTE :=
  if s is String c s then cons_tuple (charToBYTE c) (stringToTupleBYTE s)
  else nil_tuple _.

Definition stringToSeqBYTE (s: string) : seq BYTE :=
  stringToTupleBYTE s.

Notation "#x y" := (fromHex y) (at level 0).
Notation "#b y" := (fromBin y) (at level 0).
Notation "#c y" := (fromString y : BYTE) (at level 0).


Example fortytwo  := #42 : BYTE.
Example fortytwo1 := #x"2A".
Example fortytwo2 := #b"00101010".
Example fortytwo3 := #c"*".