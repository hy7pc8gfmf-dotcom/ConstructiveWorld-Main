Set Printing Width 500.
(* ============================================================ *)
(* UpReqWeakTriangle.v —— 席 EXP-D3B：前向 KL 弱三角真形·实施席（相位=编译重） *)
(*   2026-09-17 · 前棒 EXP-D3 高质量交接件落盘编译（报告 attn/_texpd3_交付报告-20260917.md §2/§3） *)
(*                                                                *)
(* 【公理面】零 Axiom / 零 Admitted / 零 Abort / 零 Hypothesis 位；       *)
(*   语句面全 Set（real_le_b UpRealLeB:72 / real_eq / real_lt / sigT）；  *)
(*   文尾 Print Assumptions 审计（零 magic=零公理）。红线四条自审通过。   *)
(*                                                                *)
(* 【方向声明段】（任务书 G2 的 c 定义为假命题，本文件采用修正真形）       *)
(*   任务书/EXPD1 脚本版 c := min(q_s/r_s) 为【假】：解析反例              *)
(*   Q=(1/2,1/2), R=(9/10,1/10), P=(0,1) 使 RHS-LHS=ln(3/5)<0，           *)
(*   近退化采样违反 77/3000（attn/_texpd3_sanity.py 第 1/3 节）。          *)
(*   真形（EXPD1 报告 2.2 文字段）：                                      *)
(*     KL(p||r) <=_B KL(p||q) + KL(q||r) + log(1/c)，c := min_s(r_s/q_s)， *)
(*   证书取逐点乘法形 c·q_s <= r_s（Real 层 real_le 形，免除法）。         *)
(*   修正版压测违反 0/20000（同脚本第 2 节）。逐点路线：q_s/r_s <= 1/c    *)
(*   ⟹ log 单调（real_log_le_mono）⟹ 加权求和保序（real_list_sum_le）。   *)
(*   KL 符号顺序逐处核对：kl_term 首槽=加权分布（p 或 q），全部前向。      *)
(*                                                                *)
(* 【交付清单（wtl_ 前缀全库零撞名，前棒 grep 双验）】                    *)
(*   G1①  wtl_qdiv_pos             Q 层除法正性             [非平凡低]    *)
(*   G1①  wtl_min_ratio_lb         min 证书下界（Prop）     [非平凡低]    *)
(*   G1①  wtl_min_ratio_pos        min 证书正性（Prop）     [非平凡低]    *)
(*   G1②  wtl_ratio_cert + wtl_min_ratio_cert_set  sigT 交付账 [非平凡低] *)
(*   G2    wtl_cond_triangle       条件化弱三角主件         [非平凡中]    *)
(*   G2    wtl_family              sigT 封口账              [装配]        *)
(*   G3    CS 权渡形/unique-max 特例：挂账（需 Real 平方族引擎，          *)
(*         EXPD3 报告 §2 已探明需求面；本席预算内不 attempt）。           *)
(*                                                                *)
(* 【对报告 §2/§3 的三处诚实偏差（编译期实读核出，已就地修正）】          *)
(*   1. Qlt_bool/Qlt_bool_iff/Qle_ltb 不在 QArith_base（仅 micromega 有   *)
(*      Qlt_bool，避重不 Require）：正性证改 Qlt 0 c（Prop）；             *)
(*      false 支翻向改走 Z.leb_gt 展开（DTPT.v:1746 同款先例）。          *)
(*   2. Qmult_inv_r 前提为 Qeq 形 ~ x == 0（非 Leibniz <>），Hq0 同形。    *)
(*   3. G1 sigT 交付件正性证用 Qlt 0 c（Prop 件）；可计算部分=witness c    *)
(*      （wtl_min_ratio l）+ Qle_bool 逐点下界检查，诚实标注。            *)
(*                                                                *)
(* 【引擎链（全只读消费，签名逐一实读核验）】CW219：S08 real_kl_term/      *)
(*   real_log_div/real_list_sum_le/real_list_sum_linear_r；S07 RealSetoid  *)
(*   （real_le_compat/real_le_id_l/real_le_id_r/real_eq_mult_compat/      *)
(*   real_eq_plus_compat）+ 顶层 real_le_mult_compat/real_le_plus_compat/ *)
(*   real_mult_positive；S02 real_mult_comm/assoc/one、real_plus_assoc/   *)
(*   comm；G01 real_log_le_mono；UpRealLeB real_le_b/real_le_to_le_b；     *)
(*   UpReqPinskerTransport pnt_le_b_refl/eq_r/trans/add_r/pnt_mult_inv_r/  *)
(*   pnt_list_gibbs_b；UpReqForwardKLFamily fkl_path_split_sum（消费供体）。*)
(*   禁碰件未 Require。                                                   *)
(* 编译：coqc（9.1 钉源 COQLIB=ROCQLIB=C:/Rocq-Platform~9.1~2026.01/      *)
(*   lib/coq）-q -native-compiler no -Q . "" UpReqWeakTriangle（cwd=Live_X，*)
(*   cpu_guard 包装）。                                                   *)
(* ============================================================ *)

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround.
From Stdlib Require Import Lia.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import UpReqPinskerTransport.
Require Import UpReqForwardKLFamily.

Open Scope Q_scope.

(* ================================================================ *)
(* G1：Q 层 min 证书（c := min_s(r_s/q_s) 的构造性下界与正性）        *)
(* ================================================================ *)

(* ---- 0. 证书量：l 上逐点比 r/q 的扫描最小值（nil 支取 1，空载退化） ---- *)
Fixpoint wtl_min_ratio (l : list (Q * Q)) : Q :=
  match l with
  | nil => 1
  | (q, r) :: rest =>
      let m := wtl_min_ratio rest in
      if Qle_bool (r / q) m then (r / q) else m
  end.

Definition wtl_qrat (qr : Q * Q) : Q := (snd qr) / (fst qr).

(* ---- 1. 除法正性：0<q、0<r ⟹ 0<r/q（Qmult_lt_r×Qmult_inv_r 机械链） ---- *)
Lemma wtl_qdiv_pos : forall q r : Q, Qlt 0 q -> Qlt 0 r -> Qlt 0 (r / q).
Proof.
  intros q r Hq Hr. unfold Qdiv.
  assert (Hq0 : ~ q == 0).
  { intro Hz. exact (Qlt_not_eq 0 q Hq (Qeq_sym q 0 Hz)). }
  assert (Hinv : / q * q == 1).
  { apply (Qeq_trans (/ q * q) (q * / q) 1).
    - apply Qmult_comm.
    - apply Qmult_inv_r. exact Hq0. }
  apply (proj1 (Qmult_lt_r 0 (r * / q) q Hq)).
  rewrite <- Qmult_assoc. rewrite Hinv.
  rewrite (Qmult_0_l q). rewrite (Qmult_1_r r). exact Hr.
Qed.

(* ---- 2. min 证书下界：qr ∈ l ⟹ wtl_min_ratio l ≤ r_q/q_q ---- *)
Lemma wtl_min_ratio_lb : forall (l : list (Q * Q)) (qr : Q * Q),
  In qr l -> Qle (wtl_min_ratio l) (wtl_qrat qr).
Proof.
  intros l. induction l as [| [a b] rest IH]; intros qr Hin.
  - destruct Hin.
  - simpl in Hin. simpl. destruct Hin as [Heq | Hin].
    + replace (wtl_qrat qr) with (b / a)
        by (unfold wtl_qrat; rewrite <- Heq; reflexivity).
      destruct (Qle_bool (b / a) (wtl_min_ratio rest)) eqn:E.
      * apply Qle_refl.
      * apply Qlt_le_weak. unfold Qlt.
        unfold Qle_bool in E. apply Z.leb_gt in E. exact E.
    + destruct (Qle_bool (b / a) (wtl_min_ratio rest)) eqn:E.
      * eapply Qle_trans.
        -- apply Qle_bool_iff. exact E.
        -- apply IH. exact Hin.
      * apply IH. exact Hin.
Qed.

(* ---- 3. min 证书正性：逐点正 ⟹ 0 < wtl_min_ratio l ---- *)
Lemma wtl_min_ratio_pos : forall l : list (Q * Q),
  (forall qr : Q * Q, In qr l -> Qlt 0 (fst qr)) ->
  (forall qr : Q * Q, In qr l -> Qlt 0 (snd qr)) ->
  Qlt 0 (wtl_min_ratio l).
Proof.
  intros l. induction l as [| [a b] rest IH]; intros Hq Hr.
  - unfold Qlt. simpl. lia.
  - simpl. destruct (Qle_bool (b / a) (wtl_min_ratio rest)) eqn:E.
    + exact (wtl_qdiv_pos a b (Hq (a, b) (or_introl eq_refl))
                         (Hr (a, b) (or_introl eq_refl))).
    + apply IH.
      * intros qr0 Hin0. exact (Hq qr0 (or_intror Hin0)).
      * intros qr0 Hin0. exact (Hr qr0 (or_intror Hin0)).
Qed.

(* ---- 4. G1 Set/sigT 交付账：正性 + 逐点 Qle_bool 下界可计算证书 ---- *)
(*   witness=可计算 Q（wtl_min_ratio l）；正性证=Qlt（Prop，诚实标注）；   *)
(*   下界证=逐点 Qle_bool 等式（bool 可计算检查）。                       *)
Definition wtl_ratio_cert (l : list (Q * Q)) : Type :=
  sigT (fun c : Q =>
    sigT (fun _ : Qlt 0 c =>
      forall qr : Q * Q, In qr l -> Qle_bool c (wtl_qrat qr) = true)).

Theorem wtl_min_ratio_cert_set : forall l : list (Q * Q),
  (forall qr : Q * Q, In qr l -> Qlt 0 (fst qr)) ->
  (forall qr : Q * Q, In qr l -> Qlt 0 (snd qr)) ->
  wtl_ratio_cert l.
Proof.
  intros l Hq Hr.
  refine (existT _ (wtl_min_ratio l) (existT _ _ _)).
  - exact (wtl_min_ratio_pos l Hq Hr).
  - intros qr Hin.
    exact (proj2 (Qle_bool_iff (wtl_min_ratio l) (wtl_qrat qr))
                  (wtl_min_ratio_lb l qr Hin)).
Qed.

(* ================================================================ *)
(* G2：Real 层条件化弱三角主件                                        *)
(*   KL(p||r) <=_B KL(p||q) + KL(q||r) + log(1/c)，证书 c·q_s ≤ r_s。  *)
(*   （c := min_s(r_s/q_s) 的逻辑内容；系数层由 G1 证书供给。）        *)
(* ================================================================ *)

Theorem wtl_cond_triangle : forall (Y : Type) (m : list Y) (p q r : Y -> Real)
  (c : Real)
  (Hp : forall s : Y, real_lt real_zero (p s))
  (Hq : forall s : Y, real_lt real_zero (q s))
  (Hr : forall s : Y, real_lt real_zero (r s))
  (Hnp : real_eq (real_list_sum Y p m) real_one)
  (Hnq : real_eq (real_list_sum Y q m) real_one)
  (Hnr : real_eq (real_list_sum Y r m) real_one)
  (Hc : real_lt real_zero c)
  (Hcert : forall s : Y, real_le (real_mult c (q s)) (r s)),
  real_le_b
    (real_list_sum Y (fun s : Y => real_kl_term (p s) (r s) (Hp s) (Hr s)) m)
    (real_plus
       (real_list_sum Y (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
       (real_plus
          (real_list_sum Y (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s)) m)
          (real_log (real_inv_pos c Hc) (real_inv_pos_pos c Hc)))).
Proof.
  intros Y m p q r c Hp Hq Hr Hnp Hnq Hnr Hc Hcert.
  set (L := real_inv_pos c Hc).
  set (Llog := real_log L (real_inv_pos_pos c Hc)).
  (* 步 1a：证书消 inv —— q_s·inv(r_s) ≤ L := inv(c)。
     路线：c·q_s ≤ r_s 两边乘 L·inv(r_s)（正性证书 real_mult_positive），
     左端 (c·q_s)·(L·ir) == c·((q_s·ir)·L) == q_s·ir（pnt_mult_inv_r），
     右端 r_s·(L·ir) == L（pnt_mult_inv_r）。 *)
  assert (HqrL : forall s : Y,
    real_le (real_mult (q s) (real_inv_pos (r s) (Hr s))) L).
  { intro s.
    apply (RealSetoid.real_le_compat
             (real_mult (real_mult c (q s))
                        (real_mult L (real_inv_pos (r s) (Hr s))))
             (real_mult (q s) (real_inv_pos (r s) (Hr s)))
             (real_mult (r s) (real_mult L (real_inv_pos (r s) (Hr s))))
             L).
    - (* (c·q_s)·(L·ir) == q_s·ir：assoc/comm 三步 + pnt_mult_inv_r *)
      apply (real_eq_trans
               (real_mult (real_mult c (q s))
                          (real_mult L (real_inv_pos (r s) (Hr s))))
               (real_mult c
                  (real_mult (q s)
                             (real_mult L (real_inv_pos (r s) (Hr s)))))).
      + exact (real_eq_sym _ _
                 (real_mult_assoc c (q s)
                    (real_mult L (real_inv_pos (r s) (Hr s))))).
      + apply (real_eq_trans
                 (real_mult c
                    (real_mult (q s)
                               (real_mult L (real_inv_pos (r s) (Hr s)))))
                 (real_mult c
                    (real_mult (q s)
                               (real_mult (real_inv_pos (r s) (Hr s)) L)))).
        * apply (RealSetoid.real_eq_mult_compat
                   c (real_mult (q s) (real_mult L (real_inv_pos (r s) (Hr s))))
                   c (real_mult (q s)
                                (real_mult (real_inv_pos (r s) (Hr s)) L))).
          -- apply real_eq_refl.
          -- apply (RealSetoid.real_eq_mult_compat
                     (q s) (real_mult L (real_inv_pos (r s) (Hr s)))
                     (q s) (real_mult (real_inv_pos (r s) (Hr s)) L)).
            ++ apply real_eq_refl.
            ++ exact (real_mult_comm L (real_inv_pos (r s) (Hr s))).
        * apply (real_eq_trans
                   (real_mult c
                      (real_mult (q s)
                                 (real_mult (real_inv_pos (r s) (Hr s)) L)))
                   (real_mult c
                      (real_mult (real_mult (q s) (real_inv_pos (r s) (Hr s)))
                                 L))).
          -- apply (RealSetoid.real_eq_mult_compat
                     c (real_mult (q s)
                                (real_mult (real_inv_pos (r s) (Hr s)) L))
                     c (real_mult (real_mult (q s) (real_inv_pos (r s) (Hr s)))
                                  L)).
            ++ apply real_eq_refl.
            ++ exact (real_mult_assoc (q s) (real_inv_pos (r s) (Hr s)) L).
          -- exact (pnt_mult_inv_r c
                     (real_mult (q s) (real_inv_pos (r s) (Hr s))) Hc).
    - (* r_s·(L·ir) == L（逐字 pnt_mult_inv_r） *)
      exact (pnt_mult_inv_r (r s) L (Hr s)).
    - (* 证书原形 c·q_s ≤ r_s 两边乘正量 L·ir *)
      exact (real_le_mult_compat (real_mult c (q s)) (r s)
               (real_mult L (real_inv_pos (r s) (Hr s)))
               (real_mult_positive L (real_inv_pos (r s) (Hr s))
                  (real_inv_pos_pos c Hc) (real_inv_pos_pos (r s) (Hr s)))
               (Hcert s)). }
  (* 步 1b：逐点 log 单调升权 —— p_s·(log q_s − log r_s) ≤ p_s·log(1/c)。
     路线：real_le_mult_compat（权 p_s>0）+ real_log_div 换形 +
     real_log_le_mono（q_s·inv r_s ≤ L 由步 1a）。 *)
  assert (Hpt : forall s : Y,
    real_le (real_mult (p s)
               (real_plus (real_log (q s) (Hq s))
                          (real_opp (real_log (r s) (Hr s)))))
            (real_mult (p s) Llog)).
  { intro s.
    apply (RealSetoid.real_le_compat
             (real_mult
                (real_plus (real_log (q s) (Hq s))
                           (real_opp (real_log (r s) (Hr s)))) (p s))
             (real_mult (p s)
                (real_plus (real_log (q s) (Hq s))
                           (real_opp (real_log (r s) (Hr s)))))
             (real_mult Llog (p s))
             (real_mult (p s) Llog)).
    - exact (real_mult_comm
               (real_plus (real_log (q s) (Hq s))
                          (real_opp (real_log (r s) (Hr s)))) (p s)).
    - exact (real_mult_comm Llog (p s)).
    - apply (real_le_mult_compat
               (real_plus (real_log (q s) (Hq s))
                          (real_opp (real_log (r s) (Hr s))))
               Llog (p s) (Hp s)).
      exact (RealSetoid.real_le_compat
               (real_log (real_mult (q s) (real_inv_pos (r s) (Hr s)))
                  (real_mult_positive (q s) (real_inv_pos (r s) (Hr s))
                     (Hq s) (real_inv_pos_pos (r s) (Hr s))))
               (real_plus (real_log (q s) (Hq s))
                          (real_opp (real_log (r s) (Hr s))))
               Llog Llog
               (real_log_div (q s) (r s) (Hq s) (Hr s))
               (real_eq_refl Llog)
               (real_log_le_mono (real_mult (q s) (real_inv_pos (r s) (Hr s)))
                  L
                  (real_mult_positive (q s) (real_inv_pos (r s) (Hr s))
                     (Hq s) (real_inv_pos_pos (r s) (Hr s)))
                  (real_inv_pos_pos c Hc)
                  (HqrL s))). }
  (* 步 2：求和保序 ΣRes ≤ Σ(p·log(1/c)) *)
  assert (Hs2 : real_le
    (real_list_sum Y (fun s : Y =>
       real_mult (p s)
         (real_plus (real_log (q s) (Hq s))
                    (real_opp (real_log (r s) (Hr s))))) m)
    (real_list_sum Y (fun s : Y => real_mult (p s) Llog) m)).
  { apply real_list_sum_le. intro s. exact (Hpt s). }
  (* 步 3：归一化收腿 Σ(p·log(1/c)) == log(1/c)（real_list_sum_linear_r + Hnp） *)
  assert (Hs3 : real_eq
    (real_list_sum Y (fun s : Y => real_mult (p s) Llog) m) Llog).
  { apply (real_eq_trans
             (real_list_sum Y (fun s : Y => real_mult (p s) Llog) m)
             (real_mult Llog (real_list_sum Y p m))).
    - exact (real_list_sum_linear_r Y Llog p m).
    - apply (real_eq_trans
               (real_mult Llog (real_list_sum Y p m))
               (real_mult Llog real_one)).
      + exact (RealSetoid.real_eq_mult_compat Llog (real_list_sum Y p m)
                 Llog real_one
                 (real_eq_refl Llog) Hnp).
      + exact (real_mult_one Llog). }
  assert (Hs4 : real_le
    (real_list_sum Y (fun s : Y =>
       real_mult (p s)
         (real_plus (real_log (q s) (Hq s))
                    (real_opp (real_log (r s) (Hr s))))) m) Llog).
  { exact (RealSetoid.real_le_id_r
             (real_list_sum Y (fun s : Y =>
                real_mult (p s)
                  (real_plus (real_log (q s) (Hq s))
                             (real_opp (real_log (r s) (Hr s))))) m)
             (real_list_sum Y (fun s : Y => real_mult (p s) Llog) m)
             Llog Hs3 Hs2). }
  (* 步 4+5：fkl_path_split_sum 链式 + 加法保序 ⟹ ΣKL(p||r) ≤ ΣKL(p||q)+log(1/c) *)
  assert (Hs5 : real_le
    (real_list_sum Y (fun s : Y => real_kl_term (p s) (r s) (Hp s) (Hr s)) m)
    (real_plus
       (real_list_sum Y (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
       Llog)).
  { apply (real_le_trans
             (real_list_sum Y
                (fun s : Y => real_kl_term (p s) (r s) (Hp s) (Hr s)) m)
             (real_plus
                (real_list_sum Y
                   (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
                (real_list_sum Y (fun s : Y =>
                   real_mult (p s)
                     (real_plus (real_log (q s) (Hq s))
                                (real_opp (real_log (r s) (Hr s))))) m))
             (real_plus
                (real_list_sum Y
                   (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
                Llog)).
    - exact (RealSetoid.real_le_id_l
               (real_list_sum Y
                  (fun s : Y => real_kl_term (p s) (r s) (Hp s) (Hr s)) m)
               (real_plus
                  (real_list_sum Y
                     (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
                  (real_list_sum Y (fun s : Y =>
                     real_mult (p s)
                       (real_plus (real_log (q s) (Hq s))
                                  (real_opp (real_log (r s) (Hr s))))) m))
               (real_plus
                  (real_list_sum Y
                     (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
                  (real_list_sum Y (fun s : Y =>
                     real_mult (p s)
                       (real_plus (real_log (q s) (Hq s))
                                  (real_opp (real_log (r s) (Hr s))))) m))
               (fkl_path_split_sum Y m p q r Hp Hq Hr)
               (real_le_refl
                  (real_plus
                     (real_list_sum Y
                        (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s))
                        m)
                     (real_list_sum Y (fun s : Y =>
                        real_mult (p s)
                          (real_plus (real_log (q s) (Hq s))
                                     (real_opp (real_log (r s) (Hr s)))))
                        m)))).
    - exact (real_le_plus_compat
               (real_list_sum Y
                  (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
               (real_list_sum Y
                  (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
               (real_list_sum Y (fun s : Y =>
                  real_mult (p s)
                    (real_plus (real_log (q s) (Hq s))
                               (real_opp (real_log (r s) (Hr s))))) m)
               Llog
               (real_le_refl
                  (real_list_sum Y
                     (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m))
               Hs4). }
  (* 步 7a：重排 (A+log(1/c))+C == A+(C+log(1/c))（assoc+comm 显式链） *)
  assert (Hreord : real_eq
    (real_plus
       (real_plus
          (real_list_sum Y
             (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
          Llog)
       (real_list_sum Y
          (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s)) m))
    (real_plus
       (real_list_sum Y
          (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
       (real_plus
          (real_list_sum Y
             (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s)) m)
          Llog))).
  { apply (real_eq_trans
             (real_plus
                (real_plus
                   (real_list_sum Y
                      (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
                   Llog)
                (real_list_sum Y
                   (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s)) m))
             (real_plus
                (real_list_sum Y
                   (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
                (real_plus Llog
                   (real_list_sum Y
                      (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s))
                      m)))).
    - exact (real_eq_sym _ _
               (real_plus_assoc
                  (real_list_sum Y
                     (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
                  Llog
                  (real_list_sum Y
                     (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s))
                     m))).
    - exact (RealSetoid.real_eq_plus_compat
               (real_list_sum Y
                  (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
               (real_plus Llog
                  (real_list_sum Y
                     (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s))
                     m))
               (real_list_sum Y
                  (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
               (real_plus
                  (real_list_sum Y
                     (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s))
                     m)
                  Llog)
               (real_eq_refl
                  (real_list_sum Y
                     (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s))
                     m))
               (real_plus_comm Llog
                  (real_list_sum Y
                     (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s))
                     m))). }
  (* 步 6+7b：升 Bishop + Gibbs 非负腿 + pnt 组合封口 *)
  apply (pnt_le_b_trans
           (real_list_sum Y
              (fun s : Y => real_kl_term (p s) (r s) (Hp s) (Hr s)) m)
           (real_plus
              (real_list_sum Y
                 (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
              Llog)
           (real_plus
              (real_list_sum Y
                 (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
              (real_plus
                 (real_list_sum Y
                    (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s)) m)
                 Llog))).
  - exact (real_le_to_le_b _ _ Hs5).
  - exact (pnt_le_b_eq_r
             (real_plus
                (real_list_sum Y
                   (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
                Llog)
             (real_plus
                (real_plus
                   (real_list_sum Y
                      (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
                   Llog)
                (real_list_sum Y
                   (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s)) m))
             (real_plus
                (real_list_sum Y
                   (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
                (real_plus
                   (real_list_sum Y
                      (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s))
                      m)
                   Llog))
             Hreord
             (pnt_le_b_add_r
                (real_plus
                   (real_list_sum Y
                      (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
                   Llog)
                (real_plus
                   (real_list_sum Y
                      (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
                   Llog)
                (real_list_sum Y
                   (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s)) m)
                (pnt_list_gibbs_b Y m q r Hq Hr Hnq Hnr)
                (pnt_le_b_refl
                   (real_plus
                      (real_list_sum Y
                         (fun s : Y =>
                            real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
                      Llog)))).
Qed.

(* ================================================================ *)
(* G2 封口件：wtl 族 sigT 账（照 fkl_family 模式）                    *)
(* ================================================================ *)
Definition wtl_leg_min_cert : Type := forall l : list (Q * Q),
  (forall qr : Q * Q, In qr l -> Qlt 0 (fst qr)) ->
  (forall qr : Q * Q, In qr l -> Qlt 0 (snd qr)) ->
  wtl_ratio_cert l.

(* 注：含 (Y : Type) 量词，落 Type 层（与 fkl_leg_path_sum 同型注记）。 *)
Definition wtl_leg_cond_triangle : Type := forall (Y : Type) (m : list Y)
  (p q r : Y -> Real) (c : Real)
  (Hp : forall s : Y, real_lt real_zero (p s))
  (Hq : forall s : Y, real_lt real_zero (q s))
  (Hr : forall s : Y, real_lt real_zero (r s))
  (Hnp : real_eq (real_list_sum Y p m) real_one)
  (Hnq : real_eq (real_list_sum Y q m) real_one)
  (Hnr : real_eq (real_list_sum Y r m) real_one)
  (Hc : real_lt real_zero c)
  (Hcert : forall s : Y, real_le (real_mult c (q s)) (r s)),
  real_le_b
    (real_list_sum Y (fun s : Y => real_kl_term (p s) (r s) (Hp s) (Hr s)) m)
    (real_plus
       (real_list_sum Y (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
       (real_plus
          (real_list_sum Y (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s)) m)
          (real_log (real_inv_pos c Hc) (real_inv_pos_pos c Hc)))).

Theorem wtl_family :
  sigT (fun _ : wtl_leg_min_cert => wtl_leg_cond_triangle).
Proof.
  exact (existT _ wtl_min_ratio_cert_set wtl_cond_triangle).
Qed.

(* ---- 审计位（零 magic 检查） ---- *)
Print Assumptions wtl_qdiv_pos.
Print Assumptions wtl_min_ratio_lb.
Print Assumptions wtl_min_ratio_pos.
Print Assumptions wtl_min_ratio_cert_set.
Print Assumptions wtl_cond_triangle.
Print Assumptions wtl_family.
