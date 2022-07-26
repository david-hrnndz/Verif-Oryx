Require Import VST.floyd.proofauto.
Require Import curve448.
Require Import stdpp.list.
Require Import ZArith.
Require Import compcert.lib.Coqlib.

(* /**
 * @brief Conditional swap
 * @param[in,out] a Pointer to the first integer
 * @param[in,out] b Pointer to the second integer
 * @param[in] c Condition variable
 **/

void curve448Swap(uint32_t *a, uint32_t *b, uint32_t c)
{
   uint_t i;
   uint32_t mask;
   uint32_t dummy;

   //The mask is the all-1 or all-0 word
   mask = ~c + 1;

   //Conditional swap
   for(i = 0; i < 14; i++)
   {
      //Constant time implementation
      dummy = mask & (a[i] ^ b[i]);
      a[i] ^= dummy;
      b[i] ^= dummy;
   }
}
*)

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Local Open Scope Z.

Scheme Equality for list.

Definition curve448Swap_spec : ident * funspec :=
DECLARE _curve448Swap
WITH a : val, sha : share, contents_a : list Z,
     b : val, shb : share, contents_b : list Z,
     c : Z, (* Should be 0 or 1. See PROP in PRE.  *)
     gv : globals
PRE [ tptr tuint, tptr tuint, tuint ]
    PROP   (writable_share sha; 
            writable_share shb;
            Zlength contents_a = 14;
            Zlength contents_b = 14;
            c = 0 \/ c = 1)
    PARAMS ( a ; b ; Vint(Int.repr c)) GLOBALS (gv)
    SEP    (data_at sha (tarray tuint 14) (map Vint (map Int.repr contents_a)) a;
            data_at shb (tarray tuint 14) (map Vint (map Int.repr contents_b)) b)
POST [ tvoid ]
    PROP   ()
    RETURN ()
    SEP    (data_at sha (tarray tuint 14) 
                (if (Z.eqb c 0) then (map Vint (map Int.repr contents_a))
                 else map Vint (map Int.repr contents_b)) a;
            data_at shb (tarray tuint 14) 
                (if (Z.eqb c 0) then (map Vint (map Int.repr contents_b))
                else map Vint (map Int.repr contents_a)) b). 
            (* If c = 0, no swap. Else, swap. *)

Definition curve448Swap_INV a contents_a b contents_b c:=
(EX i : Z,
(PROP   (Zlength contents_a = 14;
         Zlength contents_b = 14)
LOCAL   (temp _a a; temp _b b; temp _mask (Vint (Int.repr (((c + 1) mod 2) - 1))))
SEP     ( (* What is the loop invariant? 
                Idea: 
                 If c = 0, then a = a and b = b.
                 If c = 1, then a and b are partially swapped up to index i. *)
         if (Z.eqb c 0) then (
            data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_a)) a
         )
         else  (
            data_at Tsh (tarray tuint 14) 
            ((sublist.sublist 0 i (map Vint (map Int.repr contents_b)))
            ++ sublist.sublist i 14 (map Vint (map Int.repr contents_a)))
            a
               );
         if (Z.eqb c 0) then (
            data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_b)) b
         )
         else (
            data_at Tsh (tarray tuint 14) 
            ((sublist.sublist 0 i (map Vint (map Int.repr contents_a)))
            ++ sublist.sublist i 14 (map Vint (map Int.repr contents_b)))
            b
         )
        )))%assert.

Definition Gprog : funspecs := ltac:(with_library prog [ curve448Swap_spec ]).

Lemma body_curve448Swap : semax_body Vprog Gprog f_curve448Swap curve448Swap_spec.
Proof.
   start_function.
   forward.
   forward_for_simple_bound 14 (curve448Swap_INV a contents_a b contents_b c).
   entailer!.
   destruct H1.
   rewrite H1. 
   f_equal.
   autorewrite with norm. 
   replace (1 mod 2) with (1) by easy.
   replace (1-1) with (0) by easy.
   unfold Int.add.
   f_equal.
   unfold Int.unsigned.
   

        


(* TESTING THIS IN C COMPILER:

#include <stdio.h>
/**
 * @brief Conditional swap
 * @param[in,out] a Pointer to the first integer
 * @param[in,out] b Pointer to the second integer
 * @param[in] c Condition variable
 **/

typedef unsigned long uint32_t;
typedef unsigned int uint_t;
const int size = 2;
void curve448Swap(int *a, int *b, uint32_t c)
{
   uint_t i;
   uint32_t mask;
   uint32_t dummy;

   //The mask is the all-1 or all-0 word
   mask = ~c + 1;

   //Conditional swap
   for(i = 0; i < size; i++)
   {
      //Constant time implementation
      dummy = mask & (a[i] ^ b[i]);
      a[i] ^= dummy;
      b[i] ^= dummy;
   }
}
int main() {
int a[2] = {1, 2};
int b[2] = {3, 4};

curve448Swap(a,b,1);

printf("a:");
int i;
for(i=0; i < size; i++)
{
    printf("%d, ", a[i]);
}

}
*)