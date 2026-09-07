(* ===================================================================== *)
(* UpLoebD2.v — Löb 真证长线 D2：可证性账本 Σ(σ) 的构造性落地                *)
(*              （纯 Set 层 / stdlib only / 依赖 UpLoeb.v = D1 基座）         *)
(*                                                                       *)
(* 论文定位：「不完备性的构造性治理」HB D1–D3 构造性实现第二棒。              *)
(*   D1 = 对角机制（UpLoeb.v，已交付）；D2 = 本件；D3 = Löb 主定理（后续）。  *)
(*                                                                       *)
(* D2 交付四件（对应 D1 文件尾接口建议）：                                   *)
(*   §8 证明项码账与码级重演：gnPrf（证明项 → 码，标签 6/7/8，与项码 0–3、     *)
(*        公式码 4–5 在 pairp 标签空间分区互斥）+ dP2/dP（证明码的全函数       *)
(*        燃料解码器，与 dT2/dF2 同构）+ 重演主定理 gnPrf_replay：           *)
(*        凭证的码经 dP2 在任意充足燃料下重演恰回被证公式。                    *)
(*        【D1'】Prf f → ledger(⌜f⌝) 居留 = ledger_entry。                  *)
(*   §9 可证性账本：ledger_at w = sigT{ f & sigT{ pf : Prf f &               *)
(*        (w 对齐 ⌜f⌝ 的 tid 码账) * (dP 重演账) }} ——「码 w 处挂一张          *)
(*        Prf 凭证 + 双 tid 账」；凭证是一等分量随行挂载（不从码重构，         *)
(*        原理性不可能，见文末诚实边界）。                                  *)
(*   §10 MP 码级封闭【D2'】：MPc c1 c2 = pairp 7 (pairp c1 c2) ——             *)
(*        分离规则在码层封闭：两张凭证码合成的新码，其重演恰为 MP 结论          *)
(*        （MPc_code_closed 纯码层 + MPc_prf_closed/MPc_dP_closed Prf 供账）。*)
(*   §11 Σ(σ) 反射承重件：bsearch（结构递归真有界搜索，false 起点，无硬编码    *)
(*        分支）+ verPf（dP2 驱动的码级凭证验证器）+ Formula2（fsig Σ-原子，  *)
(*        语言仍无约束词栏 → substF2 无捕获 → evalF2_subst 交换律保持不破）    *)
(*        + 双向承重：账本行 ⇒ Σ-原子真（evalF2_fsig_ledger）；              *)
(*        Σ-原子真 ⇒ 低于界的码 w 其重演恰为该码公式（Sigma_bsearch_reflect）。*)
(*        dec_gnF 驱动的「码→公式」反射 = code_reflect。                     *)
(*                                                                       *)
(* 三假法对照（承 D1）：假法①（hyp 占位）——账本行挂的凭证 pf 是 Prf 归纳型     *)
(*   的真项；假法②（Triv 填充）——重演/封闭定理由 pairp/unp2/gnT_fuel/        *)
(*   gnF_fuel 真实组装，无占位收尾；假法③（量词硬编码）——bsearch 是结构       *)
(*   递归的真搜索，Sigma_fires / Sigma_bound_tight 双向 vm_compute 烟测：     *)
(*   界 3000 时真、界恰短（2623）时假——真值由界与码账真实决定。               *)
(*                                                                       *)
(* Set 层纪律：全部 D2 载体（ledger / dP2 / verPf / bsearch / Formula2 /     *)
(*   evalF2 / MPc / gnPrf）零 Prop；承重定理语句以 tid/sigT/bool 为载体。     *)
(*   唯一例外：燃料参数化定理（gnPrf_replay / MPc_code_closed）的            *)
(*   (… <= k)%nat 界前提——与 D1 已交付的 gnT_fuel / gnF_fuel 接口完全        *)
(*   同型（Proof 层算术接口，非 Set 层数据）。零公理、零承认、零占位、         *)
(*   零经典逻辑；全链信息性，可提取。                                       *)
(* ===================================================================== *)

From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

Require Import UpLoeb.

(* ===================================================================== *)
(* §8 证明项码账与码级重演                                                    *)
(*     证明项的哥德尔编码：三条规则分贴标签 6 / 7 / 8 —— 与项码标签 0–3、       *)
(*     公式码标签 4–5 互斥。ax_eqT / repl 的元级前提（赋值全称的 tid 值等）    *)
(*     不入码——由 D1 的 Prf_soundness 元级可靠性承担，诚实边界见文末。         *)
(* ===================================================================== *)

Fixpoint gnPrf (f : Formula) (pf : Prf f) {struct pf} : nat :=
  match pf in Prf f0 return nat with
  | @ax_eqT u1 u2 _ => pairp 6 (pairp (gnT u1) (gnT u2))
  | @mpF a b pf1 pf2 => pairp 7 (pairp (gnPrf (fimp a b) pf1) (gnPrf a pf2))
  | @repl th t1 t2 _ => pairp 8 (pairp (pairp (gnF th) (gnT t1)) (gnT t2))
  end.

(* 证明码的全函数解码器（燃料 = 码值，与 D1 的 dT2/dF2 同构）：
     标签 6：ax_eqT —— 两项码经 dT2 解出，重演 teq；
     标签 7：mpF   —— 两张凭证码经 dP2 解出（大前提须解为 fimp，且小前提
            重演式的码与大前提前件的码一致：gnF 比对），重演 MP 结论；
     标签 8：repl  —— th 码经 dF2、两代入项码经 dT2 解出，重演代入双条件。 *)
Fixpoint dP2 (f c : nat) {struct f} : option Formula :=
  match f with
  | O => None
  | S f' =>
      match unp2 c c with
      | Some (S (S (S (S (S (S O))))), q) =>
          (match unp2 q q with
           | Some (a, b) =>
               (match dT2 f' a with
                | Some x =>
                    (match dT2 f' b with
                     | Some y => Some (teq x y)
                     | None => None
                     end)
                | None => None
                end)
           | None => None
           end)
      | Some (S (S (S (S (S (S (S O)))))), q) =>
          (match unp2 q q with
           | Some (w1, w2) =>
               (match dP2 f' w1 with
                | Some (fimp u v) =>
                    (match dP2 f' w2 with
                     | Some z => if Nat.eqb (gnF z) (gnF u) then Some v else None
                     | None => None
                     end)
                | _ => None
                end)
           | None => None
           end)
      | Some (S (S (S (S (S (S (S (S O))))))), q) =>
          (match unp2 q q with
           | Some (p, r) =>
               (match unp2 p p with
                | Some (a, b) =>
                    (match dF2 f' a with
                     | Some th =>
                         (match dT2 f' b with
                          | Some x =>
                              (match dT2 f' r with
                               | Some y => Some (fimp (substF th x) (substF th y))
                               | None => None
                               end)
                          | None => None
                          end)
                     | None => None
                     end)
                | None => None
                end)
           | None => None
           end)
      | _ => None
      end
  end.

Definition dP (c : nat) : option Formula := dP2 c c.

(* 码级卫生烟测：证明解码器拒绝小码 / 公式码（656 = gnF (teq tzero tzero)） *)
Lemma dP_rejects_small : dP 3 = None.
Proof. reflexivity. Qed.

Lemma dP_rejects_formula_code : dP 656 = None.
Proof. reflexivity. Qed.

(* ═══ D2 主定理一（码级重演）：凭证的码经 dP2 在任意充足燃料下重演，
       恰好得到被证公式 —— D1 建议的「dT2 fuel 结构做证明项码级重演」。 ═══ *)
Theorem gnPrf_replay : forall (f : Formula) (pf : Prf f) (k : nat),
  (gnPrf f pf <= k)%nat -> tid (option Formula) (dP2 k (gnPrf f pf)) (Some f).
Proof.
  intros f pf.
  induction pf as [u1 u2 Hv | a b pf1 IH1 pf2 IH2 | th t1 t2 Hv]; intros k Hk;
    destruct k as [|k'].
  - (* ax_eqT，燃料耗尽：证明码恒正，矛盾 *)
    cbn [gnPrf pairp] in Hk. lia.
  - (* ax_eqT 主情形：两项码经 gnT_fuel 重演 *)
    cbn [gnPrf dP2].
    pose proof (pairp_ge1 (gnT u1) (gnT u2)) as Hq1.
    pose proof (pairp_ge (gnT u1) (gnT u2)) as Hq2.
    pose proof (pairp_pos (gnT u1) (gnT u2)) as Hq3.
    cbn [gnPrf pairp] in Hk.
    assert (Hb1 : (gnT u1 <= k')%nat) by lia.
    assert (Hb2 : (gnT u2 <= k')%nat) by lia.
    rewrite unp2_pair. cbv iota.
    rewrite unp2_pair. cbv iota.
    rewrite (gnT_fuel u1 k' Hb1). cbv iota.
    rewrite (gnT_fuel u2 k' Hb2). cbv iota.
    apply tid_refl.
  - (* mpF，燃料耗尽 *)
    cbn [gnPrf pairp] in Hk. lia.
  - (* mpF 主情形：两张子凭证码重演 + gnF 比对反射 *)
    cbn [gnPrf dP2].
    pose proof (pairp_ge1 (gnPrf (fimp a b) pf1) (gnPrf a pf2)) as Hq1.
    pose proof (pairp_ge (gnPrf (fimp a b) pf1) (gnPrf a pf2)) as Hq2.
    pose proof (pairp_pos (gnPrf (fimp a b) pf1) (gnPrf a pf2)) as Hq3.
    cbn [gnPrf pairp] in Hk.
    assert (Hb1 : (gnPrf (fimp a b) pf1 <= k')%nat) by lia.
    assert (Hb2 : (gnPrf a pf2 <= k')%nat) by lia.
    rewrite unp2_pair. cbv iota.
    rewrite unp2_pair. cbv iota.
    tidQ (IH1 k' Hb1) E1. rewrite E1. cbv iota.
    tidQ (IH2 k' Hb2) E2. rewrite E2. cbv iota.
    rewrite Nat.eqb_refl.
    apply tid_refl.
  - (* repl，燃料耗尽 *)
    cbn [gnPrf pairp] in Hk. lia.
  - (* repl 主情形：th 经 dF2、两代入项经 dT2，重演代入双条件 *)
    cbn [gnPrf dP2].
    pose proof (pairp_ge1 (gnF th) (gnT t1)) as Hq1.
    pose proof (pairp_ge (gnF th) (gnT t1)) as Hq2.
    pose proof (pairp_pos (gnF th) (gnT t1)) as Hq3.
    pose proof (pairp_ge1 (pairp (gnF th) (gnT t1)) (gnT t2)) as Hq4.
    pose proof (pairp_ge (pairp (gnF th) (gnT t1)) (gnT t2)) as Hq5.
    cbn [gnPrf pairp] in Hk.
    assert (Hb1 : (gnF th <= k')%nat) by lia.
    assert (Hb2 : (gnT t1 <= k')%nat) by lia.
    assert (Hb3 : (gnT t2 <= k')%nat) by lia.
    rewrite unp2_pair. cbv iota.
    rewrite unp2_pair. cbv iota.
    rewrite unp2_pair. cbv iota.
    rewrite (gnF_fuel th k' Hb1). cbv iota.
    rewrite (gnT_fuel t1 k' Hb2). cbv iota.
    rewrite (gnT_fuel t2 k' Hb3). cbv iota.
    apply tid_refl.
Qed.

(* 自燃料重演的方程形式（Proof 内部重写用） *)
Corollary gnPrf_replay_eq : forall (f : Formula) (pf : Prf f),
  dP2 (gnPrf f pf) (gnPrf f pf) = Some f.
Proof.
  intros f pf.
  tidQ (gnPrf_replay f pf (gnPrf f pf) (Nat.le_refl (gnPrf f pf))) E. exact E.
Qed.

(* dP 形式：凭证码的自燃料重演恰回被证公式（无前提） *)
Theorem Prf_replay : forall (f : Formula) (pf : Prf f),
  tid (option Formula) (dP (gnPrf f pf)) (Some f).
Proof.
  intros f pf. unfold dP.
  exact (gnPrf_replay f pf (gnPrf f pf) (Nat.le_refl (gnPrf f pf))).
Qed.

(* ===================================================================== *)
(* §9 可证性账本 Σ(σ) 的行结构                                                *)
(*     行 = 码 w 处挂：被证公式 f、Prf 凭证 pf、双 tid 码账：                   *)
(*       第一账（对齐）：w 恰为 ⌜f⌝；                                        *)
(*       第二账（重演）：pf 的证明码经 dP 重演恰回 f。                         *)
(*     D1'：Prf f → ledger(⌜f⌝) 居留 = ledger_entry。                       *)
(* ===================================================================== *)

Definition ledger_at (w : nat) : Type :=
  sigT (fun f : Formula =>
    sigT (fun pf : Prf f =>
      (tid nat w (gnF f) *
       tid (option Formula) (dP (gnPrf f pf)) (Some f))%type)).

Definition ledger : Type := sigT ledger_at.

Theorem ledger_entry : forall (f : Formula) (pf : Prf f), ledger_at (gnF f).
Proof.
  intros f pf. unfold ledger_at. exists f. exists pf. split.
  - apply tid_refl.
  - exact (Prf_replay f pf).
Qed.

Theorem ledger_inhabited : ledger.
Proof.
  unfold ledger. exists (gnF (teq tzero tzero)).
  apply (ledger_entry (teq tzero tzero)
    (ax_eqT tzero tzero (fun s : nat -> nat => @tid_refl nat (valt tzero s)))).
Qed.

(* 账本行的码齐性迁移：行不依赖代表元的选取 *)
Theorem ledger_tid_transfer : forall (w1 w2 : nat),
  tid nat w1 w2 -> ledger_at w1 -> ledger_at w2.
Proof.
  intros w1 w2 Hw Hrow. unfold ledger_at in Hrow. unfold ledger_at.
  destruct Hrow as [f [pf [H1 H2]]].
  exists f. exists pf. split.
  - apply (tid_trans nat w2 w1 (gnF f)). apply tid_sym. exact Hw. exact H1.
  - exact H2.
Qed.

(* dec_gnF 驱动的「码→公式」反射：凡与 ⌜g⌝ 对齐的码 c，反射出
   「f 的码对齐 c 且 dF c 重演恰为 f」的居留凭证 *)
Theorem code_reflect : forall (c : nat) (g : Formula),
  tid nat c (gnF g) ->
  sigT (fun f : Formula =>
    (tid nat (gnF f) c * tid (option Formula) (dF c) (Some f))%type).
Proof.
  intros c g H. exists g. split.
  - exact (tid_sym nat c (gnF g) H).
  - apply tid_eq. unfold dF. tidQ H Ec. rewrite Ec. apply dec_gnF.
Qed.

(* ===================================================================== *)
(* §10 MP 码级封闭【D2'】                                                    *)
(*     MPc：分离规则的码层合成子。封闭性 = 两张凭证码（及各自充足燃料）          *)
(*     合成的新码，在任意充足燃料下重演恰为 MP 结论；Prf 侧由 gnPrf_replay    *)
(*     直接供账。dP2 标签 7 分支的 gnF 比对在此被 Nat.eqb_refl 反射满足。      *)
(* ===================================================================== *)

Definition MPc (c1 c2 : nat) : nat := pairp 7 (pairp c1 c2).

Theorem MPc_code_closed : forall (c1 c2 : nat) (a b : Formula),
  (forall k : nat, (c1 <= k)%nat ->
     tid (option Formula) (dP2 k c1) (Some (fimp a b))) ->
  (forall k : nat, (c2 <= k)%nat ->
     tid (option Formula) (dP2 k c2) (Some a)) ->
  forall k : nat, (MPc c1 c2 <= k)%nat ->
  tid (option Formula) (dP2 k (MPc c1 c2)) (Some b).
Proof.
  intros c1 c2 a b H1 H2 k Hk. unfold MPc.
  destruct k as [|k'].
  - unfold MPc in Hk. cbn [pairp] in Hk. lia.
  - cbn [dP2].
    pose proof (pairp_ge1 c1 c2) as Hq1.
    pose proof (pairp_ge c1 c2) as Hq2.
    pose proof (pairp_pos c1 c2) as Hq3.
    unfold MPc in Hk. cbn [pairp] in Hk.
    assert (Hb1 : (c1 <= k')%nat) by lia.
    assert (Hb2 : (c2 <= k')%nat) by lia.
    rewrite unp2_pair. cbv iota.
    rewrite unp2_pair. cbv iota.
    tidQ (H1 k' Hb1) E1. rewrite E1. cbv iota.
    tidQ (H2 k' Hb2) E2. rewrite E2. cbv iota.
    rewrite Nat.eqb_refl.
    apply tid_refl.
Qed.

Theorem MPc_prf_closed : forall (a b : Formula) (pf1 : Prf (fimp a b)) (pf2 : Prf a)
  (k : nat), (gnPrf b (mpF a b pf1 pf2) <= k)%nat ->
  tid (option Formula) (dP2 k (MPc (gnPrf (fimp a b) pf1) (gnPrf a pf2))) (Some b).
Proof.
  intros a b pf1 pf2 k Hk.
  apply (MPc_code_closed (gnPrf (fimp a b) pf1) (gnPrf a pf2) a b
    (gnPrf_replay (fimp a b) pf1) (gnPrf_replay a pf2) k).
  cbn [gnPrf MPc] in Hk. exact Hk.
Qed.

(* dP 自燃料形式：MP 合成码的重演恰为结论 —— 码层 MP 封闭的干净陈述 *)
Theorem MPc_dP_closed : forall (a b : Formula) (pf1 : Prf (fimp a b)) (pf2 : Prf a),
  tid (option Formula)
    (dP (MPc (gnPrf (fimp a b) pf1) (gnPrf a pf2))) (Some b).
Proof.
  intros a b pf1 pf2.
  apply (MPc_prf_closed a b pf1 pf2 (MPc (gnPrf (fimp a b) pf1) (gnPrf a pf2))).
  unfold MPc. cbn [gnPrf]. apply Nat.le_refl.
Qed.

(* ===================================================================== *)
(* §11 Σ(σ) 反射承重件                                                       *)
(*     bsearch：真有界搜索（结构递归，false 起点，无硬编码真值分支）；           *)
(*     verPf：dP2 驱动的码级凭证验证器（「重演码 == 目标码」可判定比对）；      *)
(*     Formula2：D1 片段 + fsig（Σ-原子：界 B 下搜索凭证码验证目标码 c）。      *)
(*     语言仍无约束词栏 → substF2 无捕获问题 → evalF2_subst 交换律保持不破。    *)
(* ===================================================================== *)

Fixpoint bsearch (bd : nat) (p : nat -> bool) : bool :=
  match bd with
  | O => false
  | S b' => orb (p b') (bsearch b' p)
  end.

(* 搜索的见证完整性：真 ⇒ 存在低于界的见证 *)
Theorem bsearch_witness : forall (N : nat) (p : nat -> bool) (w : nat),
  tid bool (Nat.ltb w N) true -> tid bool (p w) true ->
  tid bool (bsearch N p) true.
Proof.
  induction N as [|N' IHN]; intros p w Hlt Hp.
  - exfalso. tidQ Hlt E. pose proof (proj1 (Nat.ltb_lt w 0) E) as Hw0. lia.
  - cbn [bsearch]. destruct (Nat.eq_dec w N') as [Heq|Hne].
    + rewrite <- Heq. tidQ Hp Ep. apply tid_eq. rewrite Ep. reflexivity.
    + assert (Hlt2 : tid bool (Nat.ltb w N') true).
      { apply tid_eq. tidQ Hlt Elt.
        pose proof (proj1 (Nat.ltb_lt w (S N')) Elt) as H1.
        apply (proj2 (Nat.ltb_lt w N')). lia. }
      apply (tid_trans bool (orb (p N') (bsearch N' p)) (orb (p N') true)).
      * exact (tid_cong (orb (p N')) (bsearch N' p) true (IHN p w Hlt2 Hp)).
      * apply tid_eq. destruct (p N'); reflexivity.
Qed.

(* 搜索的刻画：真 ⇒ 存在低于界的码其验证为真（tid/bool 载体，零 Prop） *)
Theorem bsearch_character : forall (N : nat) (p : nat -> bool),
  tid bool (bsearch N p) true ->
  sigT (fun w : nat =>
    (tid bool (Nat.ltb w N) true * tid bool (p w) true)%type).
Proof.
  induction N as [|N' IHN]; intros p H.
  - exfalso. cbn [bsearch] in H. tidQ H E. discriminate E.
  - cbn [bsearch] in H. destruct (p N') eqn:Ep.
    + exists N'. split.
      * apply tid_eq. apply (proj2 (Nat.ltb_lt N' (S N'))). lia.
      * apply tid_eq. rewrite Ep. reflexivity.
    + cbn [orb] in H.
      destruct (IHN p H) as [w [Hlt Hpw]].
      exists w. split.
      * apply tid_eq. tidQ Hlt Elt.
        pose proof (proj1 (Nat.ltb_lt w N') Elt) as H1.
        apply (proj2 (Nat.ltb_lt w (S N'))). lia.
      * exact Hpw.
Qed.

(* bsearch 的逐点 tid 同变（Σ-子句沿 tid 语义的搬运件，供 D3） *)
Theorem bsearch_tid_cong : forall (bd : nat) (p q : nat -> bool),
  (forall j : nat, tid bool (p j) (q j)) ->
  tid bool (bsearch bd p) (bsearch bd q).
Proof.
  induction bd as [|bd' IHb]; intros p q Hp.
  - apply tid_refl.
  - cbn [bsearch]. apply tid_eq.
    tidQ (Hp bd') Eh. rewrite Eh.
    tidQ (IHb p q Hp) Ei. rewrite Ei.
    reflexivity.
Qed.

(* Σ-语言：D1 片段 + Σ-原子 fsig B c
   （语义：bsearch (valt B s) (fun w => verPf w (valt c s))） *)
Inductive Formula2 : Set :=
| f2b : Formula -> Formula2
| fsig : Term -> Term -> Formula2
| fimp2 : Formula2 -> Formula2 -> Formula2.

Fixpoint substF2 (f : Formula2) (t : Term) : Formula2 :=
  match f with
  | f2b g => f2b (substF g t)
  | fsig B c => fsig (substT B t) (substT c t)
  | fimp2 a b => fimp2 (substF2 a t) (substF2 b t)
  end.

Definition verPf (w c : nat) : bool :=
  match dP2 w w with
  | Some g => Nat.eqb (gnF g) c
  | None => false
  end.

Fixpoint evalF2 (f : Formula2) (s : nat -> nat) : bool :=
  match f with
  | f2b g => evalF g s
  | fsig B c => bsearch (valt B s) (fun w : nat => verPf w (valt c s))
  | fimp2 a b => orb (negb (evalF2 a s)) (evalF2 b s)
  end.

(* ═══ D2 主定理二（交换律不破）：有界搜索语言下的 evalF_subst ═══ *)
Theorem evalF2_subst : forall (f : Formula2) (t : Term) (s : nat -> nat),
  evalF2 (substF2 f t) s = evalF2 f (upd s (valt t s)).
Proof.
  induction f as [g | B c | a IHa b IHb]; intros t s.
  - cbn [substF2 evalF2]. rewrite evalF_subst. reflexivity.
  - cbn [substF2 evalF2]. rewrite !valt_substT. reflexivity.
  - cbn [substF2 evalF2]. rewrite IHa. rewrite IHb. reflexivity.
Qed.

(* Σ(σ) 可靠性半边一：与证明码对齐的 w 必过 verPf 验证 *)
Theorem verPf_ledger_sound : forall (w : nat) (f : Formula) (pf : Prf f),
  tid nat w (gnPrf f pf) -> tid bool (verPf w (gnF f)) true.
Proof.
  intros w f pf Hw. apply tid_eq. unfold verPf.
  tidQ Hw E. rewrite E.
  rewrite (gnPrf_replay_eq f pf). cbv iota. apply Nat.eqb_refl.
Qed.

(* Σ(σ) 可靠性半边二：账本行（凭证码低于界、公式码对齐）⇒ Σ-原子为真 *)
Theorem evalF2_fsig_ledger : forall (B c : Term) (s : nat -> nat)
  (f : Formula) (pf : Prf f),
  tid bool (Nat.ltb (gnPrf f pf) (valt B s)) true ->
  tid nat (gnF f) (valt c s) ->
  tid bool (evalF2 (fsig B c) s) true.
Proof.
  intros B c s f pf Hw Hc. apply tid_eq. cbn [evalF2].
  assert (Hpw : tid bool (verPf (gnPrf f pf) (valt c s)) true).
  { apply tid_eq. unfold verPf.
    rewrite (gnPrf_replay_eq f pf). cbv iota.
    tidQ Hc Ec. rewrite Ec. apply Nat.eqb_refl. }
  tidQ (bsearch_witness (valt B s) (fun w : nat => verPf w (valt c s))
          (gnPrf f pf) Hw Hpw) Ebs.
  exact Ebs.
Qed.

(* 桥接展示：真实账本行（ax_eqT 凭证，证明码 2624）+ 界 3000 ⇒ Σ-原子真 *)
Theorem Sigma_atom_fires_via_ledger :
  tid bool (evalF2 (fsig (numT 3000) (numT (gnF (teq tzero tzero))))
              (fun _ : nat => 0)) true.
Proof.
  apply (evalF2_fsig_ledger (numT 3000) (numT (gnF (teq tzero tzero)))
    (fun _ : nat => 0) (teq tzero tzero)
    (ax_eqT tzero tzero (fun s : nat -> nat => @tid_refl nat (valt tzero s)))).
  - apply tid_eq. rewrite valt_numT.
    apply (proj2 (Nat.ltb_lt
      (gnPrf (teq tzero tzero)
        (ax_eqT tzero tzero (fun s : nat -> nat => @tid_refl nat (valt tzero s))))
      3000)).
    vm_compute. lia.
  - apply tid_eq. rewrite valt_numT. reflexivity.
Qed.

(* Σ-原子真的反射：搜出低于界的码 w，其重演恰为该码对应的公式
   （dP2 驱动；凭证重构原理上不可能——见文末诚实边界——反射给到重演层） *)
Theorem Sigma_bsearch_reflect : forall (B : nat) (g : Formula),
  tid bool (bsearch B (fun w : nat => verPf w (gnF g))) true ->
  sigT (fun w : nat =>
    (tid bool (Nat.ltb w B) true *
     sigT (fun f : Formula =>
       (tid nat (gnF f) (gnF g) *
        tid (option Formula) (dP2 w w) (Some f))%type))%type).
Proof.
  intros B g H.
  destruct (bsearch_character B (fun w : nat => verPf w (gnF g)) H)
    as [w [Hlt Hvw]].
  exists w. split.
  - exact Hlt.
  - unfold verPf in Hvw. tidQ Hvw E. cbv beta in E.
    destruct (dP2 w w) as [gg|] eqn:Ed.
    + cbv iota in E.
      pose proof (proj1 (Nat.eqb_eq (gnF gg) (gnF g)) E) as Eeq.
      exists gg. split.
      * apply tid_eq. exact Eeq.
      * apply tid_eq. reflexivity.
    + cbv iota in E. discriminate E.
Qed.

(* 真值烟测（假法③的反面证据：搜索是真的，界决定真值；
   2624 = gnPrf (teq tzero tzero) (ax_eqT …) 的证明码，
   656  = gnF (teq tzero tzero) 的公式码） *)
Lemma Sigma_fires : evalF2 (fsig (numT 3000) (numT (gnF (teq tzero tzero))))
                      (fun _ : nat => 0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma Sigma_bound_tight : evalF2 (fsig (numT 2623) (numT (gnF (teq tzero tzero))))
                      (fun _ : nat => 0) = false.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(* 诚实边界（显式声明，不硬凑）：                                            *)
(*   1. dP2/verPf 只重演「被证公式」，不重构 Prf 凭证本身：ax_eqT/repl 的       *)
(*      元级前提是赋值全称的 tid 值等（外延函数），原理上不可从码重构。          *)
(*      故账本行把凭证 pf 作为一等分量随行挂载（D1 接口建议的原样落实），        *)
(*      而 Σ-原子的反射只到「重演层」（Sigma_bsearch_reflect）。               *)
(*   2. gnPrf/dP2 的码空间分区（项 0–3 / 公式 4–5 / 证明 6–8）只保证标签        *)
(*      互斥；pairp 解码唯一性方向未在本件展开（D1 已给 unp2_pair 正向）。      *)
(*      verPf 的可靠性以「重演码 == 目标码」的可判定比对为界，足以承重          *)
(*      Σ(σ) 的有界搜索语义。                                                *)
(*   3. 燃料参数化定理（gnPrf_replay / MPc_code_closed）的 (… <= k)%nat 界      *)
(*      前提与 D1 的 gnT_fuel / gnF_fuel 同型——Proof 层算术接口，非             *)
(*      Set 层数据；其余全部语句 tid/sigT/bool 纯载体。                        *)
(*   4. D2 不追 Löb 主定理（D3）。                                           *)
(*                                                                       *)
(* D3 接口建议：                                                            *)
(*   a. 导出条件对应件已齐：ledger_entry（D1'）/ MPc_dP_closed（D2'）/         *)
(*      gnPrf_replay（编码稳定性）。下一棒：Formula2 的 gnF2/dF2b 编解码       *)
(*      往返（标签 9/10/11；fsig 的 B、c 是项槽，直接复用 gnT/gnF_fuel          *)
(*      证明术），然后 Prf(⌜·⌝) 自身的 gnF 稳定性。                           *)
(*   b. Σ(σ) 完备半边：把 Sigma_bsearch_reflect 的 w 反升格为凭证行，           *)
(*      需把 ax_eqT/repl 前提的元级 tid 值等替换为可判定的码级证书             *)
(*      （如限制 ax_eqT 到闭项对并配 dT2 证书；repl 配 (th,t1,t2) 的           *)
(*      dF2/dT2 证书三元组）——这是账本升为语言内可证性谓词的关键一步。          *)
(*   c. bsearch_tid_cong 可把 Σ-子句沿 tid 语义搬运；evalF2_subst 已保证       *)
(*      代入交换；Löb 句 diagF2 := substF2 (wrap2 th) (numT (gnF2 (wrap2 th))) *)
(*      的对角组装可直接照抄 D1 §7 的 repl + 码恒等 + 值恒等三件套。            *)
(* ===================================================================== *)
