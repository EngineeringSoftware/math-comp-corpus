
Reserved Notation "e .[ x ]"
  (at level 2, left associativity, format "e .[ x ]").

Reserved Notation "e .[ x1 , x2 , .. , xn ]" (at level 2, left associativity,
  format "e '[ ' .[ x1 , '/'  x2 , '/'  .. , '/'  xn ] ']'").

Reserved Notation "s `_ i" (at level 3, i at level 2, left associativity,
  format "s `_ i").
Reserved Notation "x ^-1" (at level 3, left associativity, format "x ^-1").

Reserved Notation "x *+ n" (at level 40, left associativity).
Reserved Notation "x *- n" (at level 40, left associativity).
Reserved Notation "x ^+ n" (at level 29, left associativity).
Reserved Notation "x ^- n" (at level 29, left associativity).

Reserved Notation "x *: A" (at level 40).
Reserved Notation "A :* x" (at level 40).

Reserved Notation "A :&: B"  (at level 48, left associativity).
Reserved Notation "A :|: B" (at level 52, left associativity).
Reserved Notation "a |: A" (at level 52, left associativity).
Reserved Notation "A :\: B" (at level 50, left associativity).
Reserved Notation "A :\ b" (at level 50, left associativity).

Reserved Notation "<< A >>"  (at level 0, format "<< A >>").
Reserved Notation "<[ a ] >"  (at level 0, format "<[ a ] >").

Reserved Notation "''C' [ x ]" (at level 8, format "''C' [ x ]").
Reserved Notation "''C_' A [ x ]"
  (at level 8, A at level 2, format "''C_' A [ x ]").
Reserved Notation "''C' ( A )" (at level 8, format "''C' ( A )").
Reserved Notation "''C_' B ( A )"
  (at level 8, B at level 2, format "''C_' B ( A )").
Reserved Notation "''Z' ( A )" (at level 8, format "''Z' ( A )").
Reserved Notation "''C_' ( A ) [ x ]" (at level 8, only parsing).
Reserved Notation "''C_' ( B ) ( A )" (at level 8, only parsing).

Reserved Notation "m %/ d" (at level 40, no associativity).
Reserved Notation "m %% d" (at level 40, no associativity).
Reserved Notation "m %| d" (at level 70, no associativity).
Reserved Notation "m = n %[mod d ]" (at level 70, n at next level,
  format "'[hv ' m '/'  =  n '/'  %[mod  d ] ']'").
Reserved Notation "m == n %[mod d ]" (at level 70, n at next level,
  format "'[hv ' m '/'  ==  n '/'  %[mod  d ] ']'").
Reserved Notation "m <> n %[mod d ]" (at level 70, n at next level,
  format "'[hv ' m '/'  <>  n '/'  %[mod  d ] ']'").
Reserved Notation "m != n %[mod d ]" (at level 70, n at next level,
  format "'[hv ' m '/'  !=  n '/'  %[mod  d ] ']'").

Reserved Notation "a ^` ()" (at level 8, format "a ^` ()").
Reserved Notation "a ^` ( n )" (at level 8, format "a ^` ( n )").

Reserved Notation  "`| x |" (at level 0, x at level 99, format "`| x |").

Reserved Notation "x <= y ?= 'iff' c" (at level 70, y, c at next level,
  format "x '[hv'  <=  y '/'  ?=  'iff'  c ']'").

Reserved Notation "x <= y :> T" (at level 70, y at next level).
Reserved Notation "x >= y :> T" (at level 70, y at next level, only parsing).
Reserved Notation "x < y :> T" (at level 70, y at next level).
Reserved Notation "x > y :> T" (at level 70, y at next level, only parsing).
Reserved Notation "x <= y ?= 'iff' c :> T" (at level 70, y, c at next level,
  format "x '[hv'  <=  y '/'  ?=  'iff'  c  :> T ']'").