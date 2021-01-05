### Lists

#### pair

##### pair( x,y )

```
Inductive natprod : Type :=
| pair (n1 n2 : nat).
```

##### fst

```
Definition fst (p : natprod) : nat :=
  match p with
  | pair x y ⇒ x
  end.
```

##### snd

```
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y ⇒ y
  end.
```

##### swap_pair

```
Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) ⇒ (y,x)
  end.
```

##### surjective_pairing

```
Theorem surjective_pairing : ∀ (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.
```

##### snd_fst_is_swap

```
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
```

##### fst_swap_is_snd

```
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
```

#### natlist

##### natlist

```
Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).
```

```
Notation "x :: l" := (cons x l)
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].
```

##### repeat

```
Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O ⇒ nil
  | S count' ⇒ n :: (repeat n count')
  end.
```

##### Length

```
Fixpoint length (l:natlist) : nat :=
  match l with
  | nil ⇒ O
  | h :: t ⇒ S (length t)
  end.
```

##### Append( x++y )

```
Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil ⇒ l2
  | h :: t ⇒ h :: (app t l2)
  end.
```

##### hd

```
Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil ⇒ default
  | h :: t ⇒ h
  end.
```

##### tl

```
Definition tl (l : natlist) : natlist :=
  match l with
  | nil ⇒ nil
  | h :: t ⇒ t
  end.
```

##### nonzeros

```
Fixpoint nonzeros (l:natlist) : natlist
 :=
 match l with
  | nil => nil
  | O :: l' => nonzeros l'
  | h :: l' => h :: (nonzeros l')
  end.
```

##### oddmembers

```
Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => if (evenb h) then oddmembers t
              else h :: (oddmembers t)
  end.
```

##### countoddmembers

```
Fixpoint countoddmembers (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => if (evenb h) then countoddmembers t
              else S (countoddmembers t)
  end.
```

##### alternate

```
Fixpoint alternate (l1 l2 : natlist) : natlist
:=   match l1 with
  | nil => l2
  | h :: t => 
      match l2 with 
      | nil => l1
      | h' :: t' => h :: h' :: (alternate t t')
      end
  end.
```

##### nil_app

```
Theorem nil_app : ∀ l : natlist,
  [] ++ l = l.
```

##### tl_length_pred

```
Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity.  Qed.
```

##### app_assoc

较大的列表可以推到较小的列表，直到nil

```
Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite → IHl1'. reflexivity. Qed.
```

##### rev

```
Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil ⇒ nil
  | h :: t ⇒ rev t ++ [h]
  end
```

##### app_length

```
Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
```

##### rev_length

```
Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length.
    simpl. rewrite -> IHl'. rewrite plus_comm.
    reflexivity.
Qed.
```

##### app_nil_r

```
Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
```

##### rev_app_distr

```
Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
```

##### rev_involutive

```
Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
```

##### app_assoc4

```
Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
```

##### nonzeros_app

```
Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
```

##### eqblist

```
Fixpoint eqblist (l1 l2 : natlist) : bool
:=   match l1 with
  | nil => match l2 with
           | nil => true
           | _ :: _ => false
           end
  | h :: t => match l2 with
              | nil => false
              | h' :: t' => andb (eqb h h') 
                                (eqblist t t')
              end
  end.
```

##### eqblist_refl

```
Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
```

##### eqb_ref

```
Lemma eqb_ref : forall n : nat,
 eqb n n = true.
```

##### eqb_refl

```
Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
```

##### rev_injective

```
Theorem rev_injective : forall (l1 l2 : natlist),
    rev l1 = rev l2 -> l1 = l2.
Proof.
 intros l1 l2 e.
 assert (H: rev (rev l1) = rev (rev l2)).
 { rewrite e. reflexivity. }
 rewrite rev_involutive in H. rewrite rev_involutive in H.
 rewrite H. reflexivity.
Qed.
```



#### bags

##### bags

```
Definition bag := natlist.
```

##### count

```
Fixpoint count (v : nat) (s : bag) : nat
:=   match s with
  | nil => O
  | h :: t =>
    if eqb v h then S (count v t)
    else count v t
  end.
```

##### sum

```
Definition sum : bag -> bag -> bag:=
fun l1 l2 => l1++l2.
```

##### add

```
Definition add (v : nat) (s : bag) : bag:=
v::s.
```

##### member

```
Definition member (v : nat) (s : bag) : bool:=
leb 1 (count v s).
```

##### remove_one

```
Fixpoint remove_one (v : nat) (s : bag) : bag:=
match s with
|nil => nil
|h::t => if eqb v h then t else h::(remove_one v t)
end.
```

##### remove_all

```
Fixpoint remove_all (v:nat) (s:bag) : bag:=
match s with
|nil => nil
|h::t => if eqb v h then remove_all v t else h::(remove_all v t)
end.
```

##### subset

```
Fixpoint subset (s1 : bag) (s2 : bag) : bool:=
match s1 with
|nil => true
|h::t => andb (leb (count h s1) (count h s2)) (subset t s2)
end.
```

##### total

```
Fixpoint total (s : bag) : nat :=
  match s with
  | [] => 0
  | h :: t => h + total t
  end.
```

##### max

```
Fixpoint max (s : bag) : nat :=
  match s with
  | [] => 0
  | h :: t => let v := max t in
              if h <? v then v else h
  end.
```

##### count_member_nonezero

```
Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
```

##### remove_does_not_increase_count

```
Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
```

#### natoption

##### natoption

```
Inductive natoption : Type :=
  | Some (n : nat)
  | None.
```

##### nth_error

```
Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil ⇒ None
  | a :: l' ⇒ match n with
               | O ⇒ Some a
               | S n' ⇒ nth_error l' n'
               end
  end.
```

##### hd_error

```
Definition hd_error (l : natlist) : natoption
:= match l with
   | nil => None
   | h :: t => Some h
   end.
```

#### id

##### id

```
Inductive id : Type :=
  | Id (n : nat).
```

##### eqb_id

```
Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.
```

##### eqb_id_refl

```
Theorem eqb_id_refl : forall x, true = eqb_id x x.
```

#### map

##### map

```
Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

```

##### update

```
Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.
```

##### find

```
Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.
```

##### update_eq

```
Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
```

##### update_neq

```
Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
```

