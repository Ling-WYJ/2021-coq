## bascis

### 类型

接下来需要导入`String`

```coq
From Coq Require Export String.
```

#### Booleans

##### bool

```coq
Inductive bool : Type :=
  | true
  | false.
```

##### negb

```
Definition negb (b:bool) : bool :=
  match b with
  | true ⇒ false
  | false ⇒ true
  end.
```

##### andb( && )

```
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true ⇒ b2
  | false ⇒ false
  end.
```

##### orb( || )

```
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true ⇒ true
  | false ⇒ b2
  end.
```

##### nanb

如果其输入中的一个或两个都为false，则返回true。

```
Definition nandb (b1:bool) (b2:bool) : bool:=
 match b1,b2 with
| true, true => false
| false, _  =>true
| true,false =>true
end.
```

##### andb3

当其所有输入均为true时，此函数应返回true，否则返回false。

```
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool:=
 match b1,b2,b3 with
| true,true,true => true
| _, _ ,_=> false
end.

```

##### negb_involutive

```coq
Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
```

##### andb_commutative

```
Theorem andb_commutative : forall b c, andb b c = andb c b.
```

##### andb3_exchange

```
Theorem andb3_exchange :
  ∀ b c d, andb (andb b c) d = andb (andb b d) c.
```

#####  andb_true_elim2

```
Theorem andb_true_elim2 : ∀ b c : bool,
  andb b c = true → c = true.
```

##### andb_eq_orb

```
Theorem andb_eq_orb :
  ∀ (b c : bool),
  (andb b c = orb b c) →
  b = c.
```



#### Numbers

大写字母O的构造函数表示零。当将S构造函数应用于自然数n的表示形式时，结果是n + 1的表示形式，其中S表示“继任者”。这是完整的数据类型定义。

##### nat

```
Inductive nat : Type :=
  | O
  | S (n : nat).
```

##### pred

```
Definition pred (n : nat) : nat :=
  match n with
    | O ⇒ O
    | S n' ⇒ n'
  end.
```

##### evenb

```
Fixpoint evenb (n:nat) : bool :=
  match n with
  | O ⇒ true
  | S O ⇒ false
  | S (S n') ⇒ evenb n'
  end.
```

##### oddb

```
Definition oddb (n:nat) : bool :=
  negb (evenb n).
```

##### plus( + )

```
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O ⇒ m
    | S n' ⇒ S (plus n' m)
  end.
```

##### mult( * )

```
Fixpoint mult (n m : nat) : nat :=
  match n with
    | O ⇒ O
    | S n' ⇒ plus m (mult n' m)
  end.
```

##### minus( - )

```
Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ ⇒ O
  | S _ , O ⇒ n
  | S n', S m' ⇒ minus n' m'
  end.
```

##### exp

```
Fixpoint exp (base power : nat) : nat :=
  match power with
    | O ⇒ S O
    | S p ⇒ mult base (exp base p)
  end.
```

##### factorial

```
Fixpoint factorial (n:nat) : nat:=
match n with
|O => S O
|S n' => mult n (factorial n')
end.

```

##### eqb( =? )

```
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O ⇒ match m with
         | O ⇒ true
         | S m' ⇒ false
         end
  | S n' ⇒ match m with
            | O ⇒ false
            | S m' ⇒ eqb n' m'
            end
  end.
```

##### eqb_ref

```
Lemma eqb_ref : forall n : nat,
 eqb n n = true.
```



##### leb( <=? )

```
Fixpoint leb (n m : nat) : bool :=
  match n with
  | O ⇒ true
  | S n' ⇒
      match m with
      | O ⇒ false
      | S m' ⇒ leb n' m'
      end
  end.
```

##### ltb( <? )

```
Definition ltb (n m : nat) : bool:=
negb(eqb n m)&&(leb n m).
```

##### plus_O_n

```
Theorem plus_O_n : ∀ n : nat, 0 + n = n.
```

##### plus_1_l

```
Theorem plus_1_l : forall n:nat, 1 + n = S n.
```

##### mult_0_l

```
Theorem mult_0_l : forall n:nat, 0 * n = 0.
```

##### plus_id_example

```
Theorem plus_id_example : ∀ n m:nat,
  n = m →
  n + n = m + m.
```

##### plus_id_exercise

```
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
```

##### mult_n_O

```
Check mult_n_O.
(* ===> forall n : nat, 0 = n * 0 *)
```

##### mult_n_Sm

```
(* ===> forall n m : nat, n * m + n = n * S m *)
```

#####  mult_n_0_m_0

```
Theorem mult_n_0_m_0 : ∀ p q : nat,
  (p × 0) + (q × 0) = 0.
```

#####  plus_1_neq_0

```
Theorem plus_1_neq_0 : ∀ n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.
```

##### leb_n_Sn

```
Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
```



