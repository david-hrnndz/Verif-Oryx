Require Import VST.floyd.proofauto.
Require Import stdpp.list.
Require Import ZArith.
Require Import compcert.lib.Coqlib.
Require Import list_lemmas.


(*  Function to split a [large] integer into a list representation 
    of size number of limbs (14 in this case).*)

Definition prime: Z := 2^448 - 2^224 - 1.

Local Open Scope Z. 

Fixpoint int_to_list_aux (N : Z) (i : nat) :=
    match (i) with
    | 0%nat => nil
    | S i' => [(N / (2^(32 * (13 - (Z.of_nat i'))))) mod 2^32] ++ int_to_list_aux N i'
    end.

Definition int_to_list (N : Z) : list Z := 
    int_to_list_aux N 14.

Definition two_prime_mone_list : list Z :=
    [4294967293; 4294967295; 4294967295; 4294967295; 4294967295;
       4294967295; 4294967295; 4294967293; 4294967295; 4294967295;
       4294967295; 4294967295; 4294967295; 4294967295].

Definition prime_list : list Z := 
    [2^32-1; 2^32-1; 2^32-1; 2^32-1; 2^32-1;
     2^32-1; 2^32-1; 2^32-2; 2^32-1; 2^32-1;
     2^32-1; 2^32-1; 2^32-1; 2^32-1].

Definition f_fun (l : list Z) (i t : Z) : Z:=
    if (i =? 0) then (Znth i l) + t
    else  Int.unsigned (Int.shru (Int.repr ((Znth (i-1) l) + t)) (Int.repr 32)). 

Fixpoint list_subtract (l1 l2: list Z) :=
    match l1, l2 with
    | [], _ => map (fun a => -1 * a) l2
    | _, [] => l1
    | h1::t1, h2::t2 => (h1 - h2)::list_subtract t1 t2
    end.

Fixpoint list_add_with_temp_aux (l : list Z) (temp : Z) (i : nat) :=
    match i with 
    | 0 => 
    | 

(*  Function (body) to unify the list representation of a large integer 
    so that it is an integer. *)
Fixpoint list_to_int_aux (l  : list Z) (n : Z) : Z := 
    match l with 
    | nil => 0
    | h :: t => ((h mod 2^32) * (Z.pow 2 (32 * (n)))) + (list_to_int_aux t (n+1))
    end. 

(* Function to write an integer from a list representation. *)
Definition list_to_int (l : list Z) := list_to_int_aux l 0.

Compute ((list_to_int [1;1;0;1] - list_to_int [1;0;0;3]) mod 2^(32*4)).
Compute list_to_int (list_subtract [1;1;0;1] [1;0;0;3]) mod 2^(32*4).



(* NOTE: int_to_list loses information on numbers greater than prime + 2^(32*7) -- 
         no problem if doing list_to_int (a-prime) as long as a < 2*prime.*)

Compute (prime - 2^(32*7)).

(* Definition x : Z := prime + 2^(32*7) .

Compute list_to_int (int_to_list x) - x.
Compute prime. *)


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

(* LEMMAS *)

Lemma  int_to_list_length: 
forall N : Z, 
Zlength (int_to_list N) = 14.  
Proof.
unfold int_to_list.
auto. 
Qed.

Lemma  int_to_list__list_to_int_pres_length:
forall l : list Z,  
Zlength (int_to_list (list_to_int l)) = 14.
Proof.
    intros.
    apply int_to_list_length.    
Qed.

Lemma Znth_int_to_list: 
forall (N : Z) (i : nat), 
(Z.of_nat i) < 14 ->
Znth (Z.of_nat i) (int_to_list N) = (N / (2^(32 * (Z.of_nat i)))) mod 2^32.
Proof. (* This is a manual proof by induction. *)
    intros.
    induction i as [| i _]; try easy.
    replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) by lia.
    induction i as [| i _]; try easy.
    replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) by lia.
    induction i as [| i _]; try easy;
    replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) by lia.
    induction i as [| i _]; try easy;
    replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) by lia.
    induction i as [| i _]; try easy;
    replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) by lia.
    induction i as [| i _]; try easy;
    replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) by lia.
    induction i as [| i _]; try easy;
    replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) by lia.
    induction i as [| i _]; try easy;
    replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) by lia.
    induction i as [| i _]; try easy;
    replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) by lia.
    induction i as [| i _]; try easy;
    replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) by lia.
    induction i as [| i _]; try easy;
    replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) by lia.
    induction i as [| i _]; try easy;
    replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) by lia.
    induction i as [| i _]; try easy;
    replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) by lia.
    induction i as [| i _]; try easy;
    replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) by lia.
    simpl in H. 
    replace (Z.of_nat
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S i))))))))))))))) with 14 in H by lia. 
    discriminate H. 
    Qed.
