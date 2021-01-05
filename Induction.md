### Induction

#### plus_n_O

```
Theorem plus_n_O : forall n:nat, n = n + 0.
```

#### minus_n_n

```
Theorem minus_n_n : ∀ n,
  minus n n = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite → IHn'. reflexivity. Qed.
```

#### mult_0_r 

```
Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
```

#### plus_n_Sm

```
Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
```

#### plus_comm

```
Theorem plus_comm : forall n m : nat,
  n + m = m + n.
```

#### plus_assoc

```
Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
```

#### double

```
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.
```

#### double_plus

```
Lemma double_plus : forall n, double n = n + n .
```

#### * evenb_S

```
Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
```

#### mult_0_plus'

```
Theorem mult_0_plus' : ∀ n m : nat,
  (0 + n) × m = n × m.
```

#### plus_rearrange

```
Theorem plus_rearrange : ∀ n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
```

#### plus_swap

```
Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
```

#### mult_comm

```
Theorem mult_comm : forall m n : nat,
  m * n = n * m.
```

#### * leb_refl

```
Theorem leb_refl : forall n:nat,
  true = (n <=? n).
```

#### * zero_nbeq_S

```
zero_nbeq_S : forall n:nat,
  0 =? (S n) = false.
```

#### * andb_false_r

```
Theorem andb_false_r : forall b : bool,
  andb b false = false.
```

#### plus_ble_compat_l

```
plus_ble_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
```

####  S_nbrq_0

```
Theorem S_nbeq_0 : forall n:nat,
  (S n) =? 0 = false.
```

#### mult_1_l

```
Theorem mult_1_l : forall n:nat, 1 * n = n.
```

#### mult_plus_distr_r

```
Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
```

#### mult_assoc

```
Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
```

#### *eqb_refl

```
Theorem eqb_refl : forall n : nat,
  true = (n =? n).
```

#### 