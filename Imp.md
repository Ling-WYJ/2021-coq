### Imp

#### 优化

##### try

```
Theorem silly1 : ∀ ae, aeval ae = aeval ae.
Proof. try reflexivity. (* This just does reflexivity. *) Qed.
```

##### ;

对每个分支都运用

```
Lemma foo' : ∀ n, 0 <=? n = true.
Proof.
  intros.
  (* destruct the current goal *)
  destruct n;
  (* then simpl each resulting subgoal *)
  simpl;
  (* and do reflexivity on each resulting subgoal *)
  reflexivity.
Qed.
```

##### repeat

重复使用策略

```
Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

```

