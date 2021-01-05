### Poly

#### list

##### list

```
Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).
```

##### repeat

```
Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 ⇒ nil X
  | S count' ⇒ cons X x (repeat X x count')
  end.
```

##### app

```
Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil ⇒ l2
  | cons h t ⇒ cons h (app t l2)
  end.
```

##### rev

```
Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil ⇒ nil
  | cons h t ⇒ app (rev t) (cons h nil)
  end.
```

##### length

```
Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil ⇒ 0
  | cons _ l' ⇒ S (length l')
  end.
```

##### app_nil_r

```
Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
```

##### app_assoc

```
Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
```

##### app_length

```
Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
```

##### rev_app_distr

```
Theorem rev_app_distr: ∀ X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
```

##### rev_involutive

```
Theorem rev_involutive : ∀ X : Type, ∀ l : list X,
  rev (rev l) = l.
```

#### prod

数字对的定义可以推广为多态对

##### prod( X * Y )

```
Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).
```

##### fst

```
Definition fst {X Y : Type} (p : X × Y) : X :=
  match p with
  | (x, y) ⇒ x
  end.
```

##### snd

```
Definition snd {X Y : Type} (p : X × Y) : Y :=
  match p with
  | (x, y) ⇒ y
  end.
```

##### combine

```
Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X×Y) :=
  match lx, ly with
  | [], _ ⇒ []
  | _, [] ⇒ []
  | x :: tx, y :: ty ⇒ (x, y) :: (combine tx ty)
  end.
```

##### split

```
Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y)
 :=  match l with 
  | nil => (nil, nil)
  | (x, y) :: t => (x :: fst (split t), y :: snd (split t))
  end.
```

#### Option

##### option

```
Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.
```

##### nth_error

```
Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
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
Definition hd_error {X : Type} (l : list X) : option X
 := match l with 
  | nil => None
  | h :: t => Some h 
  end.
```

#### Filter

高阶函数

##### filter

```
Fixpoint filter {X:Type} (test: X→bool) (l:list X) : (list X) :=
  match l with
  | [] ⇒ []
  | h :: t ⇒
    if test h then h :: (filter test t)
    else filter test t
  end.
```

##### countoddmembers

```
Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).
```

##### filter_even_gt7

```
Definition filter_even_gt7 (l : list nat) : list nat
:= filter (fun n => andb (evenb n) (leb 7 n)) l.
```

##### partition

```
Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X
 :=  (filter test l, filter (fun a => negb (test a)) l).
```

#### Map

##### map

```
Fixpoint map {X Y: Type} (f:X→Y) (l:list X) : (list Y) :=
  match l with
  | [] ⇒ []
  | h :: t ⇒ (f h) :: (map f t)
  end.
```

##### map_distr

```
Lemma map_distr : forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
  map f (l1 ++ l2) = (map f l1) ++ (map f l2).
Proof. intros X Y f l1 l2. induction l1 as [| h t IHt].
  - reflexivity. 
  - simpl. rewrite IHt. reflexivity.
Qed.
```

##### map_rev

```
Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
```

##### flat_map

```
Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X)
                   : (list Y)
 := match l with
  | nil => nil
  | h :: t =>  (f h) ++ (flat_map f t)
  end.
```

#### Fold

##### fold

```
Fixpoint fold {X Y: Type} (f: X→Y→Y) (l: list X) (b: Y)
                         : Y :=
  match l with
  | nil ⇒ b
  | h :: t ⇒ f h (fold f t b)
  end.
```

