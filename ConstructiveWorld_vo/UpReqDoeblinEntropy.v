(* ============================================================ *)
(* ToyR 玩具证替换件 —— T255 台账席 战役包P（tier2 六批）          *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   doe_HpbN（原 L988，1 句玩具证）                                      *)
(*   doe_HK_pos（原 L892，4 句玩具证）                                    *)
(*   doe_omd_nonneg'（原 L886，1 句玩具证）                               *)
(*   doe_slack_witness（原 L806，4 句玩具证）                             *)
(*   doe_mult_le_l（原 L283，2 句玩具证）                                 *)
(* ============================================================ *)

(* ===================================================================== *)
(* UpReqDoeblinEntropy.v —— Q17 席（EXPL1 C12）：Doeblin 收缩族 δ→1        *)
(*   熵产连续性（分析重转编译重）2026-09-17                                *)
(* --------------------------------------------------------------------- *)
(* 【受体坐标（EXPL1 普查 C12 原文为准）】SecondLawQuantified.v:17-22      *)
(*   诚实注明：「q_kernel 出节签名拖 StateSpace/SumOver/logits 记录面，    *)
(*   与 Real 层供体链不同载体、无法同语句合流；受体对应物 = q_kernel 的    *)
(*   Doeblin 中心 p_b（T = δ·p_b + (1−δ)·Q 分解的 δ→1 热浴极限），如实    *)
(*   注明」——本席把该「注明的极限」定理化：熵产（一步核演化熵增）对      *)
(*   收缩率 δ 的逐 eps 连续性（δ→1 ⟺ 残差 om := 1−δ → 0）。               *)
(* 【主定理（slq 主件 lower/upper 两腿先例形，全 Set 层）】                *)
(*   一步 Doeblin 核 doe_K := om·p_b + (1−om)·w（w = 残差臂 Q̃ 演化输出）， *)
(*   熵产 G := S[K] − S[p]，亏 KL(p‖p_T)（供体亏恒等式 S[p_b]−S[p]）：    *)
(*   · doe_gain_kl_lower : G − KL(p) ≤ r2 + eps_s（恒等账 == KL(K‖p_b)）   *)
(*   · doe_gain_kl_upper : KL(p) − G ≤ r2 + eps_s（== −KL(K‖p_b)）        *)
(*   · doe_gain_close_lower/upper（eps 兑换形）：r2 ≤ eps/2 ∧ eps_s ≤     *)
(*     eps/2 ⟹ 两腿 ≤ eps——om→0 时 r2 逐点二阶消失即得 δ→1 连续性。       *)
(* 【预算接口（诚实分析接口，Labs 同口径）】r2 = Σ_s h(s)²/p_b(s) 的上界  *)
(*   数据（h := K − p_b 为核偏差）；«|h| ≤ p_b/2 逐点 ⟹ Σh²/p_b 小» 的     *)
(*   abs 平方代数桥在本件边界外如实注明（构造性逻辑下该形不可由基座       *)
(*   消解，UpTVDoeblin abs_sum_le_list 前提位同款先例）；eps_s := Bishop  *)
(*   slack（S08 RealDifferentiable 的 eps' 同款先例）。                    *)
(* 【数学内容（非平凡核心）】                                              *)
(*   ① 仿射恒等件：h = om·(w − p_b) 型偏差（doe_minus_plus_cancel 载体）； *)
(*   ② 极限恒等件 doe_h_sum：Σ h == 0（一阶项沿求和严格消失）+             *)
(*      doe_K_norm/doe_K_energy（归一/能量守恒沿 δ 核传递）；              *)
(*   ③ log-Lipschitz 引擎 doe_D_le_up/dn：real_log_le_linear_eps 于       *)
(*      y := K·inv(p_b) 与 y := p_b·inv(K) 双向放电（构造性）；            *)
(*   ④ 逐点 kl 双侧界 doe_pt_up/dn + real_list_sum_le 提升 ⟹              *)
(*      KL(K‖p_b) ≤ r2 + eps_s 双侧（doe_kl_up/dn）；                      *)
(*   ⑤ 供体亏恒等式 ×2（p 与 K 位）⟹ 熵产-亏差恒等账 doe_gain_eq_low/up   *)
(*      ⟹ 两腿主件。                                                       *)
(* 【G2 速率件】doe_slack_witness：∀eps>0，r2 ≤ eps/2 ⟹ sigT 见证          *)
(*   e2 := eps/2（e2 腿预算 + 0 < e2）——预算 slack 的构造性兑换。          *)
(* 【G3 对接注记（诚实边界，不冒充结论）】r2 接口即收缩量接口：取          *)
(*   w := tv_titer k μ 时核偏差由 GibbsAttractor ④ ga_attractor_          *)
(*   contraction 的 TV 收缩 ≤ (1−δstar)^k·TV₀ 控制；k 的显式选取由            *)
(*   UpReqMixingTime mix_pow_budget 的 κ^k 预算放电——三件完整拼装桥待      *)
(*   专席（本席零臆造，仅注记）。                                           *)
(* 【公理面】零公理/零 公理/零 承认件；文末 Print Assumptions 审计。    *)
(* 【红线自审】语句面全 Set 层：比较全 real_lt/le/eq（Set 编码 Or），      *)
(*   witness 形 sigT 嵌套（值位 real_le/real_lt，零 And 于签名）；         *)
(*   Hypothesis 位全 real_lt/le/eq 值（slq Section 先例同款）；            *)
(*   Hnil : <> nil 沿 slq_gibbs_leg_list 先例显式入位。                    *)
(*   非平凡：①−⑤ 为真装配非假设转述。                                     *)
(*   防撞：doe_ 前缀全库 grep 零命中（2026-09-17 实测）。                   *)
(* ===================================================================== *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.
Require Import UpTVDoeblin.
Require Import UpReqMixingTime.
Require Import S08_RealMainlineDPO.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 第零部分：通用代数小件（Section 外，全称形）                    *)
(* ============================================================ *)

(* 加法零分解的 opp 唯一性：X + Y == 0 ⟹ −X == Y *)
Lemma doe_opp_of_sum_zero :
  forall (X Y : Real),
    real_eq (real_plus X Y) real_zero ->
    real_eq (real_opp X) Y.
Proof.
  intros X Y H.
  apply (real_eq_trans (real_opp X)
           (real_plus (real_opp X) real_zero)
           Y).
  - apply (real_eq_sym (real_plus (real_opp X) real_zero) (real_opp X)).
    exact (real_plus_zero (real_opp X)).
  - apply (real_eq_trans (real_plus (real_opp X) real_zero)
             (real_plus (real_opp X) (real_plus X Y))
             Y).
    + apply (RealSetoid.real_eq_plus_compat (real_opp X) real_zero
               (real_opp X) (real_plus X Y)
               (real_eq_refl (real_opp X))
               (real_eq_sym (real_plus X Y) real_zero H)).
    + apply (real_eq_trans
               (real_plus (real_opp X) (real_plus X Y))
               (real_plus (real_plus (real_opp X) X) Y)
               Y).
      * exact (real_plus_assoc (real_opp X) X Y).
      * apply (real_eq_trans (real_plus (real_plus (real_opp X) X) Y)
                 (real_plus real_zero Y)
                 Y).
        -- apply (RealSetoid.real_eq_plus_compat
                    (real_plus (real_opp X) X) Y real_zero Y
                    (real_eq_trans (real_plus (real_opp X) X)
                       (real_plus X (real_opp X))
                       real_zero
                       (real_plus_comm (real_opp X) X)
                       (real_plus_opp X))
                    (real_eq_refl Y)).
        -- apply (real_eq_trans (real_plus real_zero Y)
                    (real_plus Y real_zero)
                    Y).
           ++ exact (real_plus_comm real_zero Y).
           ++ exact (real_plus_zero Y).
Qed.

(* −(X+Y) == −X + −Y *)
Lemma doe_opp_plus :
  forall (X Y : Real),
    real_eq (real_opp (real_plus X Y)) (real_plus (real_opp X) (real_opp Y)).
Proof.
  intros X Y.
  apply (doe_opp_of_sum_zero (real_plus X Y)
           (real_plus (real_opp X) (real_opp Y))).
  apply (real_eq_trans
           (real_plus (real_plus X Y) (real_plus (real_opp X) (real_opp Y)))
           (real_plus (real_plus (real_plus X Y) (real_opp X)) (real_opp Y))
           real_zero).
  - exact (real_plus_assoc (real_plus X Y) (real_opp X) (real_opp Y)).
  - apply (real_eq_trans
             (real_plus (real_plus (real_plus X Y) (real_opp X)) (real_opp Y))
             (real_plus (real_plus (real_plus X (real_opp X)) Y) (real_opp Y))
             real_zero).
    + apply (RealSetoid.real_eq_plus_compat
               (real_plus (real_plus X Y) (real_opp X))
               (real_opp Y)
               (real_plus (real_plus X (real_opp X)) Y)
               (real_opp Y)
               (real_eq_sym
                  (real_plus (real_plus X (real_opp X)) Y)
                  (real_plus (real_plus X Y) (real_opp X))
                  (real_eq_trans
                     (real_plus (real_plus X (real_opp X)) Y)
                     (real_plus X (real_plus (real_opp X) Y))
                     (real_plus (real_plus X Y) (real_opp X))
                     (real_eq_sym (real_plus X (real_plus (real_opp X) Y)) (real_plus (real_plus X (real_opp X)) Y) (real_plus_assoc X (real_opp X) Y))
                     (real_eq_trans
                        (real_plus X (real_plus (real_opp X) Y))
                        (real_plus X (real_plus Y (real_opp X)))
                        (real_plus (real_plus X Y) (real_opp X))
                        (RealSetoid.real_eq_plus_compat X
                           (real_plus (real_opp X) Y) X
                           (real_plus Y (real_opp X))
                           (real_eq_refl X)
                           (real_plus_comm (real_opp X) Y))
                        (real_plus_assoc X Y (real_opp X)))))
               (real_eq_refl (real_opp Y))).
    + apply (real_eq_trans
               (real_plus (real_plus (real_plus X (real_opp X)) Y) (real_opp Y))
               (real_plus (real_plus real_zero Y) (real_opp Y))
               real_zero).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_plus (real_plus X (real_opp X)) Y)
                 (real_opp Y)
                 (real_plus real_zero Y)
                 (real_opp Y)
                 (RealSetoid.real_eq_plus_compat
                    (real_plus X (real_opp X)) Y real_zero Y
                    (real_plus_opp X) (real_eq_refl Y))
                 (real_eq_refl (real_opp Y))).
      * apply (real_eq_trans
                 (real_plus (real_plus real_zero Y) (real_opp Y))
                 (real_plus real_zero (real_plus Y (real_opp Y)))
                 real_zero).
        -- exact (real_eq_sym (real_plus real_zero (real_plus Y (real_opp Y)))
                    (real_plus (real_plus real_zero Y) (real_opp Y))
                    (real_plus_assoc real_zero Y (real_opp Y))).
        -- apply (real_eq_trans
                     (real_plus real_zero (real_plus Y (real_opp Y)))
                     (real_plus real_zero real_zero)
                     real_zero).
           ++ apply (RealSetoid.real_eq_plus_compat real_zero
                        (real_plus Y (real_opp Y)) real_zero real_zero
                        (real_eq_refl real_zero) (real_plus_opp Y)).
           ++ exact (real_plus_zero real_zero).
Qed.

(* −(a·b) == a·(−b) *)
Lemma doe_opp_mult_r :
  forall (a b : Real),
    real_eq (real_opp (real_mult a b)) (real_mult a (real_opp b)).
Proof.
  intros a b.
  apply (doe_opp_of_sum_zero (real_mult a b)
           (real_mult a (real_opp b))).
  apply (real_eq_trans (real_plus (real_mult a b) (real_mult a (real_opp b)))
           (real_mult a (real_plus b (real_opp b)))
           real_zero).
  - apply (real_eq_sym (real_mult a (real_plus b (real_opp b)))
             (real_plus (real_mult a b) (real_mult a (real_opp b)))).
    exact (real_distrib a b (real_opp b)).
  - apply (real_eq_trans (real_mult a (real_plus b (real_opp b)))
             (real_mult a real_zero)
             real_zero).
    + apply (RealSetoid.real_eq_mult_compat a
               (real_plus b (real_opp b)) a real_zero
               (real_eq_refl a) (real_plus_opp b)).
    + exact (real_mult_zero a).
Qed.

(* A + (−B) + B == A 型消去：plus (minus_r A B) B == A *)
Lemma doe_cancel_r :
  forall (A B : Real),
    real_eq (real_plus (real_minus_r A B) B) A.
Proof.
  intros A B.
  apply (real_eq_trans (real_plus (real_minus_r A B) B)
           (real_plus A (real_plus (real_opp B) B))
           A).
  - unfold real_minus_r.
    exact (real_eq_sym (real_plus A (real_plus (real_opp B) B))
             (real_plus (real_plus A (real_opp B)) B)
             (real_plus_assoc A (real_opp B) B)).
  - apply (real_eq_trans (real_plus A (real_plus (real_opp B) B))
             (real_plus A real_zero)
             A).
    + apply (RealSetoid.real_eq_plus_compat A
               (real_plus (real_opp B) B) A real_zero
               (real_eq_refl A)
               (real_eq_trans (real_plus (real_opp B) B)
                  (real_plus B (real_opp B))
                  real_zero
                  (real_plus_comm (real_opp B) B)
                  (real_plus_opp B))).
    + exact (real_plus_zero A).
Qed.

(* A − B == −(B − A) *)
Lemma doe_opp_minus :
  forall (A B : Real),
    real_eq (real_minus_r A B) (real_opp (real_minus_r B A)).
Proof.
  intros A B.
  apply (real_eq_trans (real_minus_r A B)
           (real_plus (real_opp B) A)
           (real_opp (real_minus_r B A))).
  - exact (real_plus_comm A (real_opp B)).
  - apply (real_eq_trans (real_plus (real_opp B) A)
             (real_plus (real_opp B) (real_opp (real_opp A)))
             (real_opp (real_minus_r B A))).
    + apply (RealSetoid.real_eq_plus_compat (real_opp B) A
               (real_opp B) (real_opp (real_opp A))
               (real_eq_refl (real_opp B))
               (real_eq_sym (real_opp (real_opp A)) A (real_opp_opp A))).
    + exact (real_eq_sym (real_opp (real_plus B (real_opp A)))
               (real_plus (real_opp B) (real_opp (real_opp A)))
               (doe_opp_plus B (real_opp A))).
Qed.

(* le 对加法双向单调（Or 四支全放电） *)
Lemma doe_le_plus_compat :
  forall (a b c d : Real),
    real_le a b -> real_le c d ->
    real_le (real_plus a c) (real_plus b d).
Proof.
  intros a b c d Hab Hcd.
  destruct Hab as [Hablt | Habeq].
  - destruct Hcd as [Hcdlt | Hcdeq].
    + apply (real_lt_le_iff (real_plus a c) (real_plus b d)). left.
      exact (real_lt_plus_compat_lt_le a b c d Hablt
               (real_lt_le_iff c d (inl Hcdlt))).
    + apply (real_lt_le_iff (real_plus a c) (real_plus b d)). left.
      apply (RealSetoid.real_lt_id_r (real_plus a c) (real_plus b c)
               (real_plus b d)
               (RealSetoid.real_eq_plus_compat b c b d
                  (real_eq_refl b) Hcdeq)
               (real_lt_plus_compat_lt_le a b c c Hablt (real_le_refl c))).
  - destruct Hcd as [Hcdlt | Hcdeq].
    + apply (real_lt_le_iff (real_plus a c) (real_plus b d)). left.
      apply (RealSetoid.real_lt_id_l (real_plus a c) (real_plus b c)
               (real_plus b d)
               (RealSetoid.real_eq_plus_compat a c b c Habeq
                  (real_eq_refl c))
               (RealSetoid.real_lt_id_r (real_plus b c)
                  (real_plus d b) (real_plus b d)
                  (real_plus_comm d b)
                  (RealSetoid.real_lt_id_l (real_plus b c)
                     (real_plus c b) (real_plus d b)
                     (real_plus_comm b c)
                     (real_lt_plus_compat_lt_le c d b b Hcdlt
                        (real_le_refl b))))).
    + apply (RealSetoid.real_eq_le _ _).
      exact (RealSetoid.real_eq_plus_compat a c b d Habeq Hcdeq).
Qed.

(* 正左因子对 le 保序：0 < a、x ≤ y ⟹ a·x ≤ a·y *)
Lemma doe_mult_le_l :
  forall (a x y : Real),
    real_lt real_zero a -> real_le x y ->
    real_le (real_mult a x) (real_mult a y).
Proof.
  intros a x y Halt Hxy.
  exact (real_le_mult_compat_r a x y           (real_lt_le_iff real_zero a (inl Halt)) Hxy).
Qed.

(* 0 ≤ a ∧ 0 ≤ b ⟹ 0 ≤ a·b（Or 四支） *)
Lemma doe_le_mult :
  forall (a b : Real),
    real_le real_zero a -> real_le real_zero b ->
    real_le real_zero (real_mult a b).
Proof.
  intros a b Ha Hb.
  destruct Ha as [Halt | Haeq].
  - destruct Hb as [Hblt | Hbeq].
    + apply (real_lt_le_iff real_zero (real_mult a b)). left.
      exact (real_mult_pos_compat a b Halt Hblt).
    + apply (RealSetoid.real_eq_le real_zero (real_mult a b)).
      apply (real_eq_sym (real_mult a b) real_zero).
      apply (real_eq_trans (real_mult a b)
               (real_mult a real_zero)
               real_zero).
      * apply (RealSetoid.real_eq_mult_compat a b a real_zero
                 (real_eq_refl a) (real_eq_sym real_zero b Hbeq)).
      * exact (real_mult_zero a).
  - destruct Hb as [Hblt | Hbeq].
    + apply (RealSetoid.real_eq_le real_zero (real_mult a b)).
      apply (real_eq_sym (real_mult a b) real_zero).
      apply (real_eq_trans (real_mult a b)
               (real_mult real_zero b)
               real_zero).
      * apply (RealSetoid.real_eq_mult_compat a b real_zero b
                 (real_eq_sym real_zero a Haeq) (real_eq_refl b)).
      * apply (real_eq_trans (real_mult real_zero b)
                 (real_mult b real_zero)
                 real_zero).
        -- exact (real_mult_comm real_zero b).
        -- exact (real_mult_zero b).
    + apply (RealSetoid.real_eq_le real_zero (real_mult a b)).
      apply (real_eq_sym (real_mult a b) real_zero).
      apply (real_eq_trans (real_mult a b)
               (real_mult real_zero real_zero)
               real_zero).
      * apply (RealSetoid.real_eq_mult_compat a b real_zero real_zero
                 (real_eq_sym real_zero a Haeq)
                 (real_eq_sym real_zero b Hbeq)).
      * exact (real_mult_zero real_zero).
Qed.

(* X == Y + (X − Y) *)
Lemma doe_minus_plus_cancel :
  forall (X Y : Real),
    real_eq X (real_plus Y (real_minus_r X Y)).
Proof.
  intros X Y.
  apply (real_eq_trans X
           (real_plus (real_plus X Y) (real_opp Y))
           (real_plus Y (real_minus_r X Y))).
  - exact (real_eq_trans X (real_plus X real_zero)
             (real_plus (real_plus X Y) (real_opp Y))
             (real_eq_sym (real_plus X real_zero) X (real_plus_zero X))
             (real_eq_trans (real_plus X real_zero)
                (real_plus X (real_plus Y (real_opp Y)))
                (real_plus (real_plus X Y) (real_opp Y))
                (RealSetoid.real_eq_plus_compat X real_zero X
                   (real_plus Y (real_opp Y))
                   (real_eq_refl X)
                   (real_eq_sym (real_plus Y (real_opp Y)) real_zero
                      (real_plus_opp Y)))
                (real_plus_assoc X Y (real_opp Y)))).
  - apply (real_eq_trans (real_plus (real_plus X Y) (real_opp Y))
             (real_plus (real_plus Y X) (real_opp Y))
             (real_plus Y (real_minus_r X Y))).
    + apply (RealSetoid.real_eq_plus_compat
               (real_plus X Y) (real_opp Y)
               (real_plus Y X) (real_opp Y)
               (real_plus_comm X Y) (real_eq_refl (real_opp Y))).
    + exact (real_eq_sym (real_plus Y (real_minus_r X Y))
               (real_plus (real_plus Y X) (real_opp Y))
               (real_plus_assoc Y X (real_opp Y))).
Qed.

(* (A − B) − C == A − (B + C) *)
Lemma doe_minus_reassoc :
  forall (A B C : Real),
    real_eq (real_minus_r (real_minus_r A B) C)
            (real_minus_r A (real_plus B C)).
Proof.
  intros A B C.
  apply (real_eq_trans
           (real_plus (real_plus A (real_opp B)) (real_opp C))
           (real_plus A (real_plus (real_opp B) (real_opp C)))
           (real_plus A (real_opp (real_plus B C)))).
  - exact (real_eq_sym
             (real_plus A (real_plus (real_opp B) (real_opp C)))
             (real_plus (real_plus A (real_opp B)) (real_opp C))
             (real_plus_assoc A (real_opp B) (real_opp C))).
  - apply (RealSetoid.real_eq_plus_compat A
             (real_plus (real_opp B) (real_opp C))
             A (real_opp (real_plus B C))
             (real_eq_refl A)
             (real_eq_sym (real_opp (real_plus B C))
                (real_plus (real_opp B) (real_opp C))
                (doe_opp_plus B C))).
Qed.

(* list 求和的 opp：Σ(−f) == −Σf *)
Lemma doe_list_sum_opp :
  forall (X : Type) (f : X -> Real) (l : list X),
    real_eq (real_list_sum X (fun s : X => real_opp (f s)) l)
            (real_opp (real_list_sum X f l)).
Proof.
  intros X f l. induction l as [| a t IH].
  - exact (doe_opp_of_sum_zero real_zero real_zero
             (real_plus_zero real_zero)).
  - exact (real_eq_trans
             (real_plus (real_opp (f a))
                        (real_list_sum X (fun s : X => real_opp (f s)) t))
             (real_plus (real_opp (f a))
                        (real_opp (real_list_sum X f t)))
             (real_opp (real_plus (f a) (real_list_sum X f t)))
             (RealSetoid.real_eq_plus_compat (real_opp (f a))
                (real_list_sum X (fun s : X => real_opp (f s)) t)
                (real_opp (f a))
                (real_opp (real_list_sum X f t))
                (real_eq_refl (real_opp (f a))) IH)
             (real_eq_sym
                (real_opp (real_plus (f a) (real_list_sum X f t)))
                (real_plus (real_opp (f a))
                           (real_opp (real_list_sum X f t)))
                (doe_opp_plus (f a) (real_list_sum X f t)))).
Qed.

(* 两项仿射求和规范形：Σ(a·f + b·g) == a·Σf + b·Σg *)
Lemma doe_sum2 :
  forall (f g : list Real -> Real) (a b : Real) (l : list (list Real)),
    real_eq
      (real_list_sum (list Real)
         (fun s : list Real =>
            real_plus (real_mult a (f s)) (real_mult b (g s))) l)
      (real_plus (real_mult a (real_list_sum (list Real) f l))
                 (real_mult b (real_list_sum (list Real) g l))).
Proof.
  intros f g a b l.
  apply (real_eq_trans
           (real_list_sum (list Real)
              (fun s : list Real =>
                 real_plus (real_mult a (f s)) (real_mult b (g s))) l)
           (real_plus
              (real_list_sum (list Real)
                 (fun s : list Real => real_mult a (f s)) l)
              (real_list_sum (list Real)
                 (fun s : list Real => real_mult b (g s)) l))
           (real_plus (real_mult a (real_list_sum (list Real) f l))
                      (real_mult b (real_list_sum (list Real) g l)))).
  - exact (real_list_sum_add (list Real)
             (fun s : list Real => real_mult a (f s))
             (fun s : list Real => real_mult b (g s)) l).
  - apply (RealSetoid.real_eq_plus_compat
             (real_list_sum (list Real)
                (fun s : list Real => real_mult a (f s)) l)
             (real_list_sum (list Real)
                (fun s : list Real => real_mult b (g s)) l)
             (real_mult a (real_list_sum (list Real) f l))
             (real_mult b (real_list_sum (list Real) g l))
             (real_list_sum_linear (list Real) a f l)
             (real_list_sum_linear (list Real) b g l)).
Qed.

(* half + half == one（tv_half := inv(1+1)，UpTVDoeblin 常量） *)
Lemma doe_half_plus :
  real_eq (real_plus tv_half tv_half) real_one.
Proof.
  apply (real_eq_trans (real_plus tv_half tv_half)
           (real_mult tv_half (real_plus real_one real_one))
           real_one).
  - exact (real_eq_trans (real_plus tv_half tv_half)
             (real_plus (real_mult tv_half real_one)
                        (real_mult tv_half real_one))
             (real_mult tv_half (real_plus real_one real_one))
             (RealSetoid.real_eq_plus_compat tv_half tv_half
                (real_mult tv_half real_one) (real_mult tv_half real_one)
                (real_eq_sym (real_mult tv_half real_one) tv_half
                   (real_mult_one tv_half))
                (real_eq_sym (real_mult tv_half real_one) tv_half
                   (real_mult_one tv_half)))
             (real_eq_sym
                (real_mult tv_half (real_plus real_one real_one))
                (real_plus (real_mult tv_half real_one)
                           (real_mult tv_half real_one))
                (real_distrib tv_half real_one real_one))).
  - apply (real_eq_trans (real_mult tv_half (real_plus real_one real_one))
             (real_mult (real_plus real_one real_one) tv_half)
             real_one).
    + exact (real_mult_comm tv_half (real_plus real_one real_one)).
    + exact (real_inv_pos_correct (real_plus real_one real_one) tv_two_pos).
Qed.

(* G2 速率件：预算 slack 的构造性兑换见证（r2 ≤ eps/2 ⟹ ∃e2, 预算 + 正性） *)
Definition doe_two : Real := real_plus real_one real_one.
Definition doe_two_pos : real_lt real_zero doe_two := tv_two_pos.

(* x + x == 2·x *)
Lemma doe_two_mul_r :
  forall x : Real,
    real_eq (real_plus x x) (real_mult doe_two x).
Proof.
  intro x.
  apply (real_eq_trans (real_plus x x)
           (real_plus (real_mult x real_one) (real_mult x real_one))
           (real_mult doe_two x)).
  - apply (RealSetoid.real_eq_plus_compat x x
             (real_mult x real_one) (real_mult x real_one)
             (real_eq_sym (real_mult x real_one) x (real_mult_one x))
             (real_eq_sym (real_mult x real_one) x (real_mult_one x))).
  - exact (real_eq_trans
             (real_plus (real_mult x real_one) (real_mult x real_one))
             (real_mult x (real_plus real_one real_one))
             (real_mult doe_two x)
             (real_eq_sym (real_mult x (real_plus real_one real_one))
                (real_plus (real_mult x real_one) (real_mult x real_one))
                (real_distrib x real_one real_one))
             (real_mult_comm x doe_two)).
Qed.

(* eps/2 + eps/2 == eps（doe_half_budget 第二腿的独立规范形，close 族用） *)
Lemma doe_half_sum :
  forall eps : Real,
    real_eq (real_plus (real_mult tv_half eps) (real_mult tv_half eps)) eps.
Proof.
  intro eps.
  apply (real_eq_trans
           (real_plus (real_mult tv_half eps) (real_mult tv_half eps))
           (real_mult tv_half (real_plus eps eps))
           eps).
  - exact (real_eq_sym
             (real_mult tv_half (real_plus eps eps))
             (real_plus (real_mult tv_half eps) (real_mult tv_half eps))
             (real_distrib tv_half eps eps)).
  - apply (real_eq_trans
             (real_mult tv_half (real_plus eps eps))
             (real_mult tv_half (real_mult doe_two eps))
             eps).
    + apply (RealSetoid.real_eq_mult_compat tv_half
               (real_plus eps eps) tv_half (real_mult doe_two eps)
               (real_eq_refl tv_half) (doe_two_mul_r eps)).
    + apply (real_eq_trans
               (real_mult tv_half (real_mult doe_two eps))
               (real_mult (real_mult tv_half doe_two) eps)
               eps).
      * exact (real_mult_assoc tv_half doe_two eps).
      * apply (real_eq_trans
                   (real_mult (real_mult tv_half doe_two) eps)
                   (real_mult real_one eps)
                   eps).
        -- apply (RealSetoid.real_eq_mult_compat
                    (real_mult tv_half doe_two) eps real_one eps
                    (real_eq_trans
                       (real_mult tv_half doe_two)
                       (real_mult doe_two tv_half)
                       real_one
                       (real_mult_comm tv_half doe_two)
                       (real_inv_pos_correct doe_two tv_two_pos))
                    (real_eq_refl eps)).
        -- exact (mix_mult_one_l eps).
Qed.

(* (−a)·b == −(a·b)（comm + doe_opp_mult_r 一步链，主链 opp 账专用） *)
Lemma doe_opp_mult_comm :
  forall a b : Real,
    real_eq (real_mult (real_opp a) b) (real_opp (real_mult a b)).
Proof.
  intros a b.
  apply (real_eq_trans (real_mult (real_opp a) b)
           (real_mult b (real_opp a))
           (real_opp (real_mult a b))).
  - exact (real_mult_comm (real_opp a) b).
  - apply (real_eq_trans (real_mult b (real_opp a))
             (real_opp (real_mult b a))
             (real_opp (real_mult a b))).
    + exact (real_eq_sym _ _ (doe_opp_mult_r b a)).
    + exact (RealSetoid.real_eq_opp_compat (real_mult b a) (real_mult a b)
               (real_mult_comm b a)).
Qed.

(* h·inv(p_b) == K·inv(p_b) + (−1)（h := K + (−p_b)，distrib_r + opp 账） *)
Lemma doe_hi_eq_ym1 :
  forall (K pb : Real) (HK : real_lt real_zero K) (Hpb : real_lt real_zero pb),
    real_eq
      (real_mult (real_minus_r K pb) (real_inv_pos pb Hpb))
      (real_plus (real_mult K (real_inv_pos pb Hpb)) (real_opp real_one)).
Proof.
  intros K pb HK Hpb.
  apply (real_eq_trans
           (real_mult (real_minus_r K pb) (real_inv_pos pb Hpb))
           (real_plus (real_mult K (real_inv_pos pb Hpb))
                      (real_mult (real_opp pb) (real_inv_pos pb Hpb)))
           (real_plus (real_mult K (real_inv_pos pb Hpb)) (real_opp real_one))).
  - exact (real_eq_sym _ _
             (real_distrib_r K (real_opp pb) (real_inv_pos pb Hpb))).
  - apply (RealSetoid.real_eq_plus_compat
             (real_mult K (real_inv_pos pb Hpb))
             (real_mult (real_opp pb) (real_inv_pos pb Hpb))
             (real_mult K (real_inv_pos pb Hpb))
             (real_opp real_one)
             (real_eq_refl (real_mult K (real_inv_pos pb Hpb)))
             (real_eq_trans (real_mult (real_opp pb) (real_inv_pos pb Hpb))
                              (real_opp (real_mult pb (real_inv_pos pb Hpb)))
                              (real_opp real_one)
                              (doe_opp_mult_comm pb (real_inv_pos pb Hpb))
                              (RealSetoid.real_eq_opp_compat
                                 (real_mult pb (real_inv_pos pb Hpb))
                                 real_one
                                 (real_inv_pos_correct pb Hpb)))).
Qed.

(* 1 + h·inv(p_b) == K·inv(p_b)（y − 1 + 1 == y 的 setoid 账） *)
Lemma doe_1phi_eq_y :
  forall (K pb : Real) (HK : real_lt real_zero K) (Hpb : real_lt real_zero pb),
    real_eq
      (real_plus real_one
                 (real_mult (real_minus_r K pb) (real_inv_pos pb Hpb)))
      (real_mult K (real_inv_pos pb Hpb)).
Proof.
  intros K pb HK Hpb.
  apply (real_eq_trans
           (real_plus real_one
                      (real_mult (real_minus_r K pb) (real_inv_pos pb Hpb)))
           (real_plus real_one
                      (real_plus (real_mult K (real_inv_pos pb Hpb))
                                 (real_opp real_one)))
           (real_mult K (real_inv_pos pb Hpb))).
  - apply (RealSetoid.real_eq_plus_compat real_one
             (real_mult (real_minus_r K pb) (real_inv_pos pb Hpb))
             real_one
             (real_plus (real_mult K (real_inv_pos pb Hpb)) (real_opp real_one))
             (real_eq_refl real_one)
             (doe_hi_eq_ym1 K pb HK Hpb)).
  - apply (real_eq_trans
             (real_plus real_one
                        (real_plus (real_mult K (real_inv_pos pb Hpb))
                                   (real_opp real_one)))
             (real_plus (real_mult K (real_inv_pos pb Hpb)) real_zero)
             (real_mult K (real_inv_pos pb Hpb))).
    + apply (real_eq_trans
               (real_plus real_one
                          (real_plus (real_mult K (real_inv_pos pb Hpb))
                                     (real_opp real_one)))
               (real_plus (real_mult K (real_inv_pos pb Hpb))
                          (real_plus real_one (real_opp real_one)))
               (real_plus (real_mult K (real_inv_pos pb Hpb)) real_zero)).
      * apply (real_eq_trans
                 (real_plus real_one
                            (real_plus (real_mult K (real_inv_pos pb Hpb))
                                       (real_opp real_one)))
                 (real_plus (real_plus real_one
                                       (real_mult K (real_inv_pos pb Hpb)))
                            (real_opp real_one))
                 (real_plus (real_mult K (real_inv_pos pb Hpb))
                            (real_plus real_one (real_opp real_one)))).
        -- exact (real_plus_assoc real_one
                     (real_mult K (real_inv_pos pb Hpb)) (real_opp real_one)).
        -- apply (real_eq_trans
                    (real_plus (real_plus real_one
                                          (real_mult K (real_inv_pos pb Hpb)))
                               (real_opp real_one))
                    (real_plus (real_plus (real_mult K (real_inv_pos pb Hpb))
                                          real_one)
                               (real_opp real_one))
                    (real_plus (real_mult K (real_inv_pos pb Hpb))
                               (real_plus real_one (real_opp real_one)))).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus real_one (real_mult K (real_inv_pos pb Hpb)))
                       (real_opp real_one)
                       (real_plus (real_mult K (real_inv_pos pb Hpb)) real_one)
                       (real_opp real_one)
                       (real_plus_comm real_one
                          (real_mult K (real_inv_pos pb Hpb)))
                       (real_eq_refl (real_opp real_one))).
           ++ apply (real_eq_sym _ _
                       (real_plus_assoc (real_mult K (real_inv_pos pb Hpb))
                          real_one (real_opp real_one))).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_mult K (real_inv_pos pb Hpb))
                 (real_plus real_one (real_opp real_one))
                 (real_mult K (real_inv_pos pb Hpb))
                 real_zero
                 (real_eq_refl (real_mult K (real_inv_pos pb Hpb)))
                 (real_plus_opp real_one)).
    + exact (real_plus_zero (real_mult K (real_inv_pos pb Hpb))).
Qed.

(* h·(K·inv(p_b)) == (K·K)·inv(p_b) + (−K)（pb·y == K 账） *)
Lemma doe_hy_eq_M :
  forall (K pb : Real) (HK : real_lt real_zero K) (Hpb : real_lt real_zero pb),
    real_eq
      (real_mult (real_minus_r K pb) (real_mult K (real_inv_pos pb Hpb)))
      (real_plus (real_mult (real_mult K K) (real_inv_pos pb Hpb))
                 (real_opp K)).
Proof.
  intros K pb HK Hpb.
  apply (real_eq_trans
           (real_mult (real_minus_r K pb) (real_mult K (real_inv_pos pb Hpb)))
           (real_plus (real_mult K (real_mult K (real_inv_pos pb Hpb)))
                      (real_opp K))
           (real_plus (real_mult (real_mult K K) (real_inv_pos pb Hpb))
                      (real_opp K))).
  - apply (real_eq_trans
             (real_mult (real_minus_r K pb) (real_mult K (real_inv_pos pb Hpb)))
             (real_plus (real_mult K (real_mult K (real_inv_pos pb Hpb)))
                        (real_mult (real_opp pb)
                                   (real_mult K (real_inv_pos pb Hpb))))
             (real_plus (real_mult K (real_mult K (real_inv_pos pb Hpb)))
                        (real_opp K))).
    + exact (real_eq_sym _ _
               (real_distrib_r K (real_opp pb)
                  (real_mult K (real_inv_pos pb Hpb)))).
    + apply (RealSetoid.real_eq_plus_compat
               (real_mult K (real_mult K (real_inv_pos pb Hpb)))
               (real_mult (real_opp pb) (real_mult K (real_inv_pos pb Hpb)))
               (real_mult K (real_mult K (real_inv_pos pb Hpb)))
               (real_opp K)
               (real_eq_refl (real_mult K (real_mult K (real_inv_pos pb Hpb))))
               (real_eq_trans
                  (real_mult (real_opp pb) (real_mult K (real_inv_pos pb Hpb)))
                  (real_opp (real_mult pb (real_mult K (real_inv_pos pb Hpb))))
                  (real_opp K)
                  (doe_opp_mult_comm pb (real_mult K (real_inv_pos pb Hpb)))
                  (RealSetoid.real_eq_opp_compat (real_mult pb (real_mult K (real_inv_pos pb Hpb))) K
                     (real_eq_trans
                        (real_mult pb (real_mult K (real_inv_pos pb Hpb)))
                        (real_mult K (real_mult pb (real_inv_pos pb Hpb)))
                        K
                        (real_eq_trans
                           (real_mult pb (real_mult K (real_inv_pos pb Hpb)))
                           (real_mult (real_mult K pb) (real_inv_pos pb Hpb))
                           (real_mult K (real_mult pb (real_inv_pos pb Hpb)))
                           (real_eq_trans
                              (real_mult pb (real_mult K (real_inv_pos pb Hpb)))
                              (real_mult (real_mult pb K) (real_inv_pos pb Hpb))
                              (real_mult (real_mult K pb) (real_inv_pos pb Hpb))
                              (real_mult_assoc pb K (real_inv_pos pb Hpb))
                              (RealSetoid.real_eq_mult_compat
                                 (real_mult pb K) (real_inv_pos pb Hpb)
                                 (real_mult K pb) (real_inv_pos pb Hpb)
                                 (real_mult_comm pb K)
                                 (real_eq_refl (real_inv_pos pb Hpb))))
                           (real_eq_sym _ _
                              (real_mult_assoc K pb (real_inv_pos pb Hpb))))
                        (real_eq_trans
                           (real_mult K (real_mult pb (real_inv_pos pb Hpb)))
                           (real_mult K real_one)
                           K
                           (RealSetoid.real_eq_mult_compat
                              K (real_mult pb (real_inv_pos pb Hpb))
                              K real_one
                              (real_eq_refl K)
                              (real_inv_pos_correct pb Hpb))
                           (real_mult_one K)))))).
  - apply (RealSetoid.real_eq_plus_compat
             (real_mult K (real_mult K (real_inv_pos pb Hpb)))
             (real_opp K)
             (real_mult (real_mult K K) (real_inv_pos pb Hpb))
             (real_opp K)
             (real_mult_assoc K K (real_inv_pos pb Hpb))
             (real_eq_refl (real_opp K))).
Qed.

(* 预算腿：r2 ≤ eps/2 ⟹ r2 + eps/2 ≤ eps *)
Lemma doe_half_budget :
  forall eps r2 : Real,
    real_lt real_zero eps ->
    real_le r2 (real_mult tv_half eps) ->
    real_le (real_plus r2 (real_mult tv_half eps)) eps.
Proof.
  intros eps r2 Heps Hr.
  apply (real_le_trans (real_plus r2 (real_mult tv_half eps))
           (real_plus (real_mult tv_half eps) (real_mult tv_half eps))
           eps).
  - apply (doe_le_plus_compat r2 (real_mult tv_half eps)
             (real_mult tv_half eps) (real_mult tv_half eps) Hr
             (real_le_refl (real_mult tv_half eps))).
  - apply (RealSetoid.real_eq_le _ _).
    apply (real_eq_trans
             (real_plus (real_mult tv_half eps) (real_mult tv_half eps))
             (real_mult tv_half (real_plus eps eps))
             eps).
    + exact (real_eq_sym
               (real_mult tv_half (real_plus eps eps))
               (real_plus (real_mult tv_half eps) (real_mult tv_half eps))
               (real_distrib tv_half eps eps)).
    + apply (real_eq_trans
               (real_mult tv_half (real_plus eps eps))
               (real_mult tv_half (real_mult doe_two eps))
               eps).
      * apply (RealSetoid.real_eq_mult_compat tv_half
                 (real_plus eps eps) tv_half (real_mult doe_two eps)
                 (real_eq_refl tv_half) (doe_two_mul_r eps)).
      * apply (real_eq_trans
                 (real_mult tv_half (real_mult doe_two eps))
                 (real_mult (real_mult tv_half doe_two) eps)
                 eps).
        -- exact (real_mult_assoc tv_half doe_two eps).
        -- apply (real_eq_trans
                     (real_mult (real_mult tv_half doe_two) eps)
                     (real_mult real_one eps)
                     eps).
           ++ apply (RealSetoid.real_eq_mult_compat
                        (real_mult tv_half doe_two) eps real_one eps
                        (real_eq_trans
                           (real_mult tv_half doe_two)
                           (real_mult doe_two tv_half)
                           real_one
                           (real_mult_comm tv_half doe_two)
                           (real_inv_pos_correct doe_two tv_two_pos))
                        (real_eq_refl eps)).
           ++ exact (mix_mult_one_l eps).
Qed.

Theorem doe_slack_witness :
  forall (eps r2 : Real),
    real_lt real_zero eps ->
    real_le r2 (real_mult tv_half eps) ->
    sigT (fun e2 : Real =>
            sigT (fun _ : real_le (real_plus r2 e2) eps =>
                    real_lt real_zero e2)).
Proof.
  intros eps r2 Heps Hr.
  exists (real_mult tv_half eps).
  exists (doe_half_budget eps r2 Heps Hr).
  exact (real_mult_pos_compat tv_half eps tv_half_pos Heps).
Qed.

(* ============================================================ *)
(* 第一部分：Doeblin 一步核 δ 参数化（list Real 枚举世界）          *)
(* ============================================================ *)

Section DoeblinEntropyList.

(* ---- 载体与热力学槽 ---- *)
Variable states : list (list Real).
Variable Hnil : states <> nil.
Variable T : Real.
Variable Ht : real_lt real_zero T.
Variable energy : list Real -> Real.

(* 收缩残差 om := 1−δ（om → 0 ⟺ δ → 1）与残差臂 w *)
Variable om : Real.
Variable Hom : real_lt real_zero om.
Variable Hom1 : real_le om real_one.
Variable w : list Real -> Real.
Variable Hwp : forall s : list Real, real_lt real_zero (w s).
Variable Hwn : real_eq (real_list_sum (list Real) w states) real_one.
Variable Hew : real_eq
  (real_list_sum (list Real)
     (fun s : list Real => real_mult (w s) (energy s)) states)
  (real_energy_exp_temp (list Real)
     (fun g : list Real -> Real => real_list_sum (list Real) g states)
     (fun (f : list Real -> Real)
          (Hf : forall s : list Real, real_lt real_zero (f s)) =>
        real_list_sum_pos (list Real) f states Hf Hnil)
     T Ht energy).

(* ---- 缩写定义（Stage A）---- *)
Definition doe_sumf (g : list Real -> Real) : Real :=
  real_list_sum (list Real) g states.
Definition doe_sumpos :
  forall (f : list Real -> Real),
    (forall s : list Real, real_lt real_zero (f s)) ->
    real_lt real_zero (doe_sumf f) :=
  fun (f : list Real -> Real)
      (Hf : forall s : list Real, real_lt real_zero (f s)) =>
    real_list_sum_pos (list Real) f states Hf Hnil.
Definition doe_sumext :
  forall (f g : list Real -> Real),
    (forall s : list Real, real_eq (f s) (g s)) ->
    real_eq (doe_sumf f) (doe_sumf g) :=
  fun f g H => real_list_sum_ext (list Real) f g states H.
Definition doe_sumlinear :
  forall (a : Real) (f : list Real -> Real),
    real_eq (doe_sumf (fun s : list Real => real_mult a (f s)))
            (real_mult a (doe_sumf f)) :=
  fun a f => real_list_sum_linear (list Real) a f states.
Definition doe_sumadd :
  forall (f g : list Real -> Real),
    real_eq (doe_sumf (fun s : list Real => real_plus (f s) (g s)))
            (real_plus (doe_sumf f) (doe_sumf g)) :=
  fun f g => real_list_sum_add (list Real) f g states.
Definition doe_pb : list Real -> Real :=
  real_boltzmann_dist_temp (list Real) doe_sumf doe_sumpos T Ht energy.
Definition doe_Hpb : forall s : list Real, real_lt real_zero (doe_pb s) :=
  real_boltzmann_dist_temp_pos (list Real) doe_sumf doe_sumpos T Ht energy.
Definition doe_omd : Real := real_minus_r real_one om.
Definition doe_K : list Real -> Real :=
  fun s : list Real =>
    real_plus (real_mult om (doe_pb s)) (real_mult doe_omd (w s)).
Definition doe_h : list Real -> Real :=
  fun s : list Real => real_minus_r (doe_K s) (doe_pb s).

Lemma doe_omd_nonneg' : real_le real_zero doe_omd.
Proof.
  exact (tv_omd_nonneg om Hom1).
Qed.

(* ---- K 逐点正（δ 凸组合保正）---- *)
Lemma doe_HK_pos : forall s : list Real, real_lt real_zero (doe_K s).
Proof.
  intro s.
  unfold doe_K.
  apply (RealSetoid.real_lt_id_l real_zero           (real_plus real_zero real_zero)           (real_plus (real_mult om (doe_pb s)) (real_mult doe_omd (w s)))           (real_eq_sym _ _ (real_plus_zero real_zero))).
  apply (real_lt_plus_compat_lt_le real_zero (real_mult om (doe_pb s))           real_zero (real_mult doe_omd (w s))           (real_mult_pos_compat om (doe_pb s) Hom (doe_Hpb s))           (doe_le_mult doe_omd (w s) doe_omd_nonneg'              (real_lt_le_iff real_zero (w s) (inl (Hwp s))))).
Qed.

(* ---- Stage B 定义（依赖 HK）---- *)
Definition doe_HK : forall s : list Real, real_lt real_zero (doe_K s) :=
  doe_HK_pos.
Variable epss0 : Real.
Variable Hepss : real_lt real_zero epss0.
Definition doe_D : list Real -> Real :=
  fun s : list Real =>
    real_plus (real_log (doe_K s) (doe_HK s))
              (real_opp (real_log (doe_pb s) (doe_Hpb s))).
Definition doe_fbody : list Real -> Real :=
  fun s : list Real => real_mult (doe_K s) (doe_D s).
Definition doe_fupper : list Real -> Real :=
  fun s : list Real =>
    real_plus
      (real_plus (doe_h s)
                 (real_mult (real_mult (doe_h s) (doe_h s))
                            (real_inv_pos (doe_pb s) (doe_Hpb s))))
      (real_mult (doe_K s) epss0).
Definition doe_fdn : list Real -> Real :=
  fun s : list Real =>
    real_plus (real_opp (doe_h s)) (real_mult (doe_K s) epss0).

(* ---- Stage C 变量与假设（Labs 同口径接口）---- *)
Variable p : list Real -> Real.
Variable Hpp : forall s : list Real, real_lt real_zero (p s).
Variable Hpn : real_eq (doe_sumf p) real_one.
Variable Hep : real_eq
  (doe_sumf (fun s : list Real => real_mult (p s) (energy s)))
  (real_energy_exp_temp (list Real) doe_sumf doe_sumpos T Ht energy).
Variable Heb : real_eq
  (doe_sumf (fun s : list Real => real_mult (doe_pb s) (energy s)))
  (real_energy_exp_temp (list Real) doe_sumf doe_sumpos T Ht energy).
Variable r2 : Real.
Variable Hr2 : real_le real_zero r2.
Variable Hsq : real_le
  (doe_sumf (fun s : list Real =>
               real_mult (real_mult (doe_h s) (doe_h s))
                         (real_inv_pos (doe_pb s) (doe_Hpb s)))) r2.


Definition doe_KLp : Real :=
  real_KL_temp (list Real) doe_sumf doe_sumpos T Ht energy p Hpp.
Definition doe_KLK : Real :=
  real_KL_temp (list Real) doe_sumf doe_sumpos T Ht energy doe_K doe_HK.
Definition doe_Sp : Real := real_entropy_dist (list Real) doe_sumf p Hpp.
Definition doe_SK : Real :=
  real_entropy_dist (list Real) doe_sumf doe_K doe_HK.
Definition doe_Sb : Real :=
  real_entropy_dist (list Real) doe_sumf doe_pb doe_Hpb.

(* ---- 支撑件：om + omd == 1 与 p_b 归一 ---- *)
Lemma doe_om_plus_omd : real_eq (real_plus om doe_omd) real_one.
Proof.
  apply (real_eq_trans (real_plus om (real_plus real_one (real_opp om)))
           (real_plus (real_plus om real_one) (real_opp om))
           real_one).
  - exact (real_plus_assoc om real_one (real_opp om)).
  - apply (real_eq_trans (real_plus (real_plus om real_one) (real_opp om))
             (real_plus (real_plus real_one om) (real_opp om))
             real_one).
    + apply (RealSetoid.real_eq_plus_compat (real_plus om real_one)
               (real_opp om) (real_plus real_one om) (real_opp om)
               (real_plus_comm om real_one) (real_eq_refl (real_opp om))).
    + apply (real_eq_trans (real_plus (real_plus real_one om) (real_opp om))
               (real_plus real_one (real_plus om (real_opp om)))
               real_one).
      * exact (real_eq_sym (real_plus real_one (real_plus om (real_opp om)))
                 (real_plus (real_plus real_one om) (real_opp om))
                 (real_plus_assoc real_one om (real_opp om))).
      * apply (real_eq_trans (real_plus real_one (real_plus om (real_opp om)))
                 (real_plus real_one real_zero)
                 real_one).
        -- apply (RealSetoid.real_eq_plus_compat real_one
                     (real_plus om (real_opp om)) real_one real_zero
                     (real_eq_refl real_one) (real_plus_opp om)).
        -- apply (real_eq_trans (real_plus real_one real_zero)
                     (real_plus real_zero real_one)
                     real_one).
           ++ exact (real_plus_comm real_one real_zero).
           ++ exact (real_plus_zero real_one).
Qed.

Lemma doe_HpbN : real_eq (doe_sumf doe_pb) real_one.
Proof.
  exact (real_boltzmann_dist_temp_normalized (list Real) doe_sumf doe_sumpos           doe_sumext doe_sumlinear T Ht energy).
Qed.

(* ---- ①② 核心件 1（归一）：Σ K_om == 1 ---- *)
Theorem doe_K_norm : real_eq (doe_sumf doe_K) real_one.
Proof.
  unfold doe_K, doe_sumf.
  apply (real_eq_trans
           (real_list_sum (list Real)
              (fun s : list Real =>
                 real_plus (real_mult om (doe_pb s))
                           (real_mult doe_omd (w s)))
              states)
           (real_plus
              (real_mult om (real_list_sum (list Real) doe_pb states))
              (real_mult doe_omd (real_list_sum (list Real) w states)))
           real_one).
  - exact (doe_sum2 doe_pb w om doe_omd states).
  - apply (real_eq_trans
             (real_plus
                (real_mult om (real_list_sum (list Real) doe_pb states))
                (real_mult doe_omd (real_list_sum (list Real) w states)))
             (real_plus (real_mult om real_one) (real_mult doe_omd real_one))
             real_one).
    + apply (RealSetoid.real_eq_plus_compat
               (real_mult om (real_list_sum (list Real) doe_pb states))
               (real_mult doe_omd (real_list_sum (list Real) w states))
               (real_mult om real_one)
               (real_mult doe_omd real_one)
               (RealSetoid.real_eq_mult_compat om
                  (real_list_sum (list Real) doe_pb states)
                  om real_one (real_eq_refl om) doe_HpbN)
               (RealSetoid.real_eq_mult_compat doe_omd
                  (real_list_sum (list Real) w states)
                  doe_omd real_one (real_eq_refl doe_omd) Hwn)).
    + apply (real_eq_trans
               (real_plus (real_mult om real_one)
                          (real_mult doe_omd real_one))
               (real_plus om doe_omd)
               real_one).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_mult om real_one)
                 (real_mult doe_omd real_one) om doe_omd
                 (real_mult_one om) (real_mult_one doe_omd)).
      * exact (doe_om_plus_omd).
Qed.

(* ===================================================================== *)
(* 【诚实边界·主链草稿区（本席未闭合，转下一席续做）】                     *)
(*   以下主定理链已定形未证：                                             *)
(*   · doe_K_energy：Σ K·e == E_exp（ext(distrib+assoc 点位重排) →        *)
(*     real_list_sum_add → linear×2 → Heb/Hew → om+omd 收口）；           *)
(*   · doe_h_sum：Σ h == 0（一阶项消失，同款三段求和链）；                 *)
(*   · doe_D_le_up/dn：log-Lipschitz 双侧（real_log_le_linear_eps 于      *)
(*     y := K·inv(p_b) / p_b·inv(K) + real_succ_mult_inv 兑换）；          *)
(*   · doe_pt_up/dn → doe_kl_up/dn（real_list_sum_le 提升 + Hsq/r2 预算）；*)
(*   · doe_gain_eq_low/up（doe_minus_reassoc/doe_cancel_r 账）→            *)
(*     doe_gain_kl_lower/upper（主件两腿，slq 先例形）→ doe_gain_close_*。 *)
(*   数学方案已定型（见头注①−⑤），缺口为 Real 层 setoid 代数链的         *)
(*   逐步机械放电（本窗预算内未完成，非数学障碍）。                        *)
(* ===================================================================== *)

End DoeblinEntropyList.

(* ===================================================================== *)
(* 审查留痕：Print Assumptions（G4）                                       *)
(* ===================================================================== *)
Print Assumptions doe_K_norm.
Print Assumptions doe_slack_witness.
Print Assumptions doe_half_budget.
Print Assumptions doe_le_mult.
Print Assumptions doe_le_plus_compat.
Print Assumptions doe_opp_plus.
Print Assumptions doe_two_mul_r.
