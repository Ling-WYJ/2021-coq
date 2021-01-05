### Logic

#### Prop

所有我们尝试证明的命题在coq中有一个类型，叫prop

#### conjunction(   /\  )

##### split

为了证明conjunction,使用split成左右两边。

如果条件里含有conjunction,可以destruct H as [HA HB]

```
Lemma and_example2 :
  ∀ n m : nat, n = 0 ∧ m = 0 → n + m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.
```

或者直接在intros的时候写成`intros n m [HA HB]`

##### and_commut

```
Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
```

##### and_assoc

```
Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
```

#### Disjunction(  \/ )

当条件里有disjunction时，此处intros的格式为intros n m [Hn | Hm].要用|隔开。

当结论里面含有disjunction的时候，可以用left或者right.

##### eq_mult_0

```
Lemma eq_mult_0 :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
```

##### or_intro_l

```
Lemma or_intro_l : forall A B : Prop, A -> A \/ B.

```

##### zero_or_succ

```
Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
```

#####  mult_eq_0 

```
Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
```

##### or_commut

```
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
```

#### ~( not )

如果我们需要证明false,我们可以使用destruct

false作为条件可以直接`intros [ ].`

##### ex_falso_quodlibet

```
Theorem ex_falso_quodlibet : ∀ (P:Prop),
  False → P.
```

##### not_implies_our_not

```
Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
```

##### not_False

```
Theorem not_False :
  ~ False.
```

##### contradiction_implies_anything

```
Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
  Proof.
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP.  Qed.
```

注意这里的apply用法，如果相反就不行，因为是在HP上使用HNA这个命题，因此是这样的顺序。

##### contrapositive

```
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
```

##### not_both_true_and_false

```
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
```

##### not_true_is_false

```
Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
```

##### True_is_true

```
Lemma True_is_true : True.
```

#### iff（ <-> ）

##### iff

```
Definition iff (P Q : Prop) := (P → Q) ∧ (Q → P).
```

在条件里出现<-> 可以用 intros A B [HA HB]

如果连接条件 和结论的是<->也可以用split,即同时要证明条件与结论的两个方向。

在结论里出现<->也可以用split证明

##### iff_sym

```
Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
```

##### not_true_iff_false

```
Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
```

##### iff_refl

```
Theorem iff_refl : forall P : Prop,
  P <-> P.
```

##### iff_trans 

```
Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
```

##### or_distributes_over_and（证明注意）

```
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
intros P Q R. split.
 - intros [HP | [HQ HR]].
    + split; left; assumption. 
    + split; right; assumption.
  - intros [[HP | HQ] [HP' | HR]].
    + left; assumption.
    + left; assumption.
    + left; assumption.
    + right. split; assumption.  
Qed.
```

##### mult_0

```
Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
```

##### or_assoc

```
Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
```

##### mult_0_3

```
Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
```

##### apply_iff_example

```
Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
```

#### even

证明exists 某个变量使得原来的命题成立

##### even

```
Definition even x := exists n : nat, x = double n.
```

```
Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm]. (* note implicit [destruct] here *)
  exists (2 + m).
  apply Hm.  Qed.
```

##### dist_not_exists

```
Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
intros X P Q. split.
  - intros [x [H | H]]. 
    + left. exists x. apply H.
    + right. exists x. apply H.
  - intros [[x Px] | [x Qx]].
    + exists x. left. apply Px.
    + exists x. right. apply Qx.
Qed.
```

#### In

##### In

```
Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.
```

##### In_map

```
Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
```

##### In_map_iff

```
Theorem In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
```

##### In_app_iff

```
Theorem In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
```

#### plus_comm新证法

直接讲参数作用到plus_comm处

##### plus_comm3_take3

```
Lemma plus_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite (plus_comm y z).
  reflexivity.
Qed.

```

##### in_not_nil

```
Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
```

##### lemma_application_ex 

```
Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
```

#### functional_extensionality

##### functional_extensionality

```
Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

```

