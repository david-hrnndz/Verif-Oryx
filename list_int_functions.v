Require Import ZArith.
Require Import stdpp.list.
Require Import VST.floyd.proofauto.

(*  Function to split a [large] integer into a list representation 
    of size number of limbs (14 in this case).*)

Local Open Scope Z. 

 Definition int_to_list (N : Z) : list Z := 
    [    N mod 2^32;             
        (N/(2^32)) mod 2^32;
        (N/(2^(32*2))) mod 2^32;
        (N/(2^(32*3))) mod 2^32;
        (N/(2^(32*4))) mod 2^32;
        (N/(2^(32*5))) mod 2^32;
        (N/(2^(32*6))) mod 2^32;
        (N/(2^(32*7))) mod 2^32;
        (N/(2^(32*8))) mod 2^32;
        (N/(2^(32*9))) mod 2^32;
        (N/(2^(32*10))) mod 2^32;
        (N/(2^(32*11))) mod 2^32;
        (N/(2^(32*12))) mod 2^32;
        (N/(2^(32*13))) mod 2^32
    ].

(*  Function (body) to unify the list representation of a large integer 
    so that it is an integer. *)
Fixpoint list_to_int' (l  : list Z) (n : Z) : Z := 
    match l with 
    | nil => 0
    | h :: t => (h * (Z.pow 2 (32 * (n)))) + (list_to_int' t (n+1))
    end. 

(* Function to write an integer from a list representation. *)
Definition list_to_int (l : list Z) := list_to_int' l 0.


(*  Checks if two lists have the same contents, where the contents are  *
 *  interpreted as Compcert's int (a Z integer taken modulo 2^32)       *)
Fixpoint list_Inteq (a b : list Z) : bool :=
    match a with 
    | [] => match b with
        | []    => true
        | _::_  => false
        end
    | a0 :: a => match b with
        | []      => false
        | b0 :: b => Int.eq (Int.repr a0) (Int.repr b0) && 
                     list_Inteq a b
        end
    end.