(* ============================================================ *)
(* UpAblP7_WallEpsChain_B.v —— 论文7 专项消融战役 席 PA7-21（W1 链身 eps 乙腿） *)
(*                                                              *)
(* 假设任务：W1 链身 eps 化（T154 申报终装遗留）——乙腿 UpReqConcMixSel 侧      *)
(*   （cmk_* 段 + 跨件合龙）。姊妹席 PA7-20 辖甲腿 UpAblP7_WallEpsChain_A.v/    *)
(*   T163（本席零接触）；本件独立自证防在飞依赖，合龙注记留 T164。              *)
(*                                                              *)
(* 母本坐标（union 根现行版实测，文件:行号）→ 消费/重建位：                     *)
(*   UpReqConcSoftmax.v:248 csm_abs_sum_le_eps（逐 eps 三角免费档）             *)
(*     → 死亡证书件的反向喂入位（eps 三角 = 墙 plain 形的逐 eps 逼近像）         *)
(*   UpReqSampling.v:116/488 abs_sum_le_h 槽与唯一深消费位 rsq_u_abs_row        *)
(*   UpReqSampling.v:499/669/1160 rsq_u_tv_contraction / rsq_u_tv_iter /        *)
(*     rsq_bounded_softmax_tv_iter（链身三节；:1153/:1166 全参投喂）            *)
(*   UpReqConcMixSel.v:856/887 cmk_attention_mixing_time/_le                    *)
(*     （:879-882/:910-913 末端消费 rsq_bounded_softmax_tv_iter）               *)
(*   UpReqConcMixSel.v:601/694 cmk_k_select/_le（构造选择器核心，首参为          *)
(*     lt_plus_compat_lt_le 诚实证书位——UpReqAlgebra ReqStrictOrderBridge       *)
(*     注记：混合加法保序不可由接口字段抽象导出；本件以 S07:6118                 *)
(*     real_lt_plus_compat_lt_le 具体层成品闭证书（ConcMixSelFeed.v:112 接线     *)
(*     先例同款），零承认。                                                     *)
(*                                                              *)
(* 链身 eps 化边界实读甄别（本件定理化对象）：                                   *)
(*   墙槽 abs_sum_le_h 在库内仅链根一次深消费（rsq_u_abs_row:488）；链身        *)
(*   （tv_contraction 以上）全部经继承吃墙——链身 eps 化的完成度边界不在墙槽       *)
(*   本身，而在「脱余量位」：逐 eps 链结论（X ≤ Y + eps 对一切 eps>0）收口到     *)
(*   plain 链结论（X ≤ Y）必须消费脱余量原理。本件以死亡证书定理化：             *)
(*   脱余量原理 ⟹ plain 墙（csm 三角 plain 形）——脱余量买下的恰是墙，边界=墙。   *)
(*   升级方向（plain ⟹ 逐 eps）另以边界引理证明可构造，两侧夹出边界位置。        *)
(*                                                              *)
(* 分级申报：                                                   *)
(*   N1 库内放电件直连：csm_abs_sum_le_eps、real_lt_plus_compat_lt_le、          *)
(*     cmk_k_select/_le、cmk_r_pow/_req_r_pow、req_r_pow、req_mult_one_l、       *)
(*     plus_zero/plus_comm/plus_assoc/mult_zero/mult_one/mult_comm/              *)
(*     mult_assoc/distrib（接口字段级）、req_plus_zero_l、req_plus_compat、      *)
(*     req_mult_compat、req_lt_id_r_loc、opp_lt_compat、plus_opp、               *)
(*     le_id_l/le_id_r/le_refl/le_trans/le_lt_trans/lt_id_r/lt_le_iff/           *)
(*     le_plus_compat/lt_plus_compat/req_lt_compat（接口字段级）。               *)
(*   N2 已证导出：ubw_b_chain_eps_iter（链身 eps 迭代镜件，余量系数               *)
(*     ubw_b_cslack 递推 c_{n+1}=1+omd·c_n 精确闭合，零 bounding 冒充）；         *)
(*     ubw_b_cmk_eps_mirror/_le（cmk 末端消费定理逐 eps 镜像，消费库选择器）。    *)
(*   N3 实例供给：两点 bool 混合号载体（正负支各一点，正性证书显式）。            *)
(*                                                              *)
(* 链身槽位诚实申报：链身单步收缩的逐 eps 形（Hstep_eps 槽）系诚实证书位          *)
(*   （同 UpReqAlgebra ReqStrictOrderBridge/AT5 槽位警告族）：其由链根            *)
(*   abs_row eps 形（T154 甲腿 uabp7we_abs_row_eps 同层）重推需穿越               *)
(*   rsq_u_tv_contraction 约 150 行 req 链，属终装 S8 范畴，本切片帽内未开工，    *)
(*   未降级未冒充——槽位假设面与库内 cmk_* 消费 rsq_bounded_softmax_tv_iter        *)
(*   的假设位同构。                                              *)
(*                                                              *)
(* 依赖清单（只读消费，原树零改）：CW_ConstructiveWorld_219、UpReqAlgebra、      *)
(*   UpReqSumD、UpReqConcSoftmax、UpReqSampling、UpReqConcMixSel；               *)
(*   具体层 = S07 RealEnhancedReal 实例（模块导入后裸名同源同解析）。             *)
(*                                                              *)
(* 红线自审：全件语句集合值面；全件真证收口；无承认件、无未证断言、无经典逻辑    *)
(*   捷径、无选择公理、无排中律；文尾逐件假设审计全封闭。                        *)
(* ============================================================ *)

From Stdlib Require Import List.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqSumD.
Require Import UpReqConcSoftmax.
Require Import UpReqSampling.
Require Import UpReqConcMixSel.
Import RealInterfaceEnhancedMod.

(* ============ §1 混合加法保序证书件（cmk 选择器首参槽位闭证书） ============ *)

(* lt a b -> le c d -> lt (a+c) (b+d)。
   消费申报：S07:6118 real_lt_plus_compat_lt_le 具体层成品直闭
   （ConcMixSelFeed.v:112 同款接线；接口 lt/le 经 RealEnhancedReal 实例
   与 real_lt/real_le 同源同解析）。此位在库内为诚实证书位
   （UpReqAlgebra ReqStrictOrderBridge：抽象层不可由接口字段导出），
   本件在具体层将其闭合，零承认。 *)
Theorem ubw_b_lt_plus_compat_lt_le : forall a b c d : Real,
  lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  exact real_lt_plus_compat_lt_le.
Qed.

(* ============ §2 小机器（req 链辅件与载体） ============ *)

(* 两点混合号载体：正支 true 点 = a（正），负支 false 点 = −b——
   plain 墙注记（UpReqConcSoftmax.v:11-16 定谳）中的混合号形状 *)
Definition ubw_b_mixed_f (a b : Real) : bool -> Real :=
  fun s : bool => if s then a else opp b.

(* 左分配律辅件：接口 distrib 字段为右分配形，左形经交换律缝合（req 链四段） *)
Lemma ubw_b_mult_plus_distr_l : forall a b c : Real,
  req (mult (plus a b) c) (plus (mult a c) (mult b c)).
Proof.
  intros a b c.
  exact (req_trans (mult (plus a b) c) (mult c (plus a b))
           (plus (mult a c) (mult b c))
           (mult_comm (plus a b) c)
           (req_trans (mult c (plus a b))
              (plus (mult c a) (mult c b))
              (plus (mult a c) (mult b c))
              (distrib c a b)
              (req_plus_compat (mult c a) (mult a c) (mult c b) (mult b c)
                 (mult_comm c a) (mult_comm c b)))).
Qed.

(* 同右端加项的非严格加法保序：le a b ⟹ le (a+c) (b+c)。
   Or 两支分案（le 定义性 = Or lt req，探针实测双向零摩擦）：
   lt 支走 §1 闭证书，req 支走 plus 同余换形。 *)
Lemma ubw_b_le_plus_r : forall a b c : Real,
  le a b -> le (plus a c) (plus b c).
Proof.
  intros a b c Hle.
  destruct Hle as [Hlt | Heq].
  - apply lt_le_iff. apply inl.
    exact (ubw_b_lt_plus_compat_lt_le a b c c Hlt (le_refl c)).
  - exact (le_id_r (plus a c) (plus a c) (plus b c)
             (req_plus_compat a b c c Heq (req_refl c))
             (le_refl (plus a c))).
Qed.

(* req 升格引理：req a b ⟹ le a b（lt_le_iff inr 支直连，绕行件） *)
Lemma ubw_b_req_le : forall a b : Real,
  req a b -> le a b.
Proof.
  intros a b Hreq.
  exact (lt_le_iff a b (inr Hreq)).
Qed.

(* ============ §3 链身 eps 化边界诚实件组 ============ *)

(* 3a 升级方向边界引理：plain 链结论 ⟹ 逐 eps 链结论（可构造方向）。
   与 3b 死亡证书构成边界两侧：升级方向免费，脱余量方向=墙。 *)
Lemma ubw_b_plain_upgrade_eps : forall X Y eps : Real,
  le X Y -> lt zero eps -> le X (plus Y eps).
Proof.
  intros X Y eps Hle Heps.
  exact (le_trans X (plus X zero) (plus Y eps)
           (req_le_plus_nonneg_r X zero (le_refl zero))
           (le_plus_compat X Y zero eps Hle (lt_le_iff zero eps (inl Heps)))).
Qed.

(* 脱余量原理（边界对象，仅以类型位出现，本件零假设它成立）：
   逐 eps 上界族收口到 plain 上界。 *)
Definition ubw_b_deslack_principle : Set :=
  forall X Y : Real,
    (forall eps : Real, lt zero eps -> le X (plus Y eps)) -> le X Y.

(* 3b 死亡证书一般形：脱余量原理 ⟹ plain 墙。
   csm 逐 eps 三角（免费档）正是墙 plain 形的逐 eps 逼近像：
   脱余量买下的恰是墙本体——链身 eps 化的完成度边界=墙。 *)
Lemma ubw_b_deslack_wall : forall (S : Set) (enum : list S) (f : S -> Real),
  ubw_b_deslack_principle ->
  le (abs (csm_sumf S enum f))
     (csm_sumf S enum (fun s : S => abs (f s))).
Proof.
  intros S enum f Hdeslack.
  apply Hdeslack.
  intros eps Heps.
  exact (csm_abs_sum_le_eps S enum f eps Heps).
Qed.

(* 3c 混合号锚：两点载体上正负支逐点定谳（sigT 打包防宇宙坑——
   Set 值面合取走依存对，T154 坑卡 1 同族） *)
Lemma ubw_b_twopt_mixed_sign : forall a b : Real,
  lt zero a -> lt zero b ->
  sigT (fun _ : lt zero (ubw_b_mixed_f a b true) =>
        lt (ubw_b_mixed_f a b false) zero).
Proof.
  intros a b Ha Hb.
  exact (existT _
           Ha
           (req_lt_id_r_loc (opp b) (opp zero) zero
              (req_trans (opp zero) (plus zero (opp zero)) zero
                 (req_sym (plus zero (opp zero)) (opp zero)
                    (req_plus_zero_l (opp zero)))
                 (plus_opp zero))
              (opp_lt_compat zero b Hb))).
Qed.

(* 3d 死亡证书打包件（PA7-12 cb2w_death_certificate 范式）：
   「脱余量原理在混合号载体上买下 plain 墙实例」×「载体确为混合号」
   双证 sigT 打包——链身 eps 化完成度边界的定理化固化。 *)
Theorem ubw_b_death_certificate : forall a b : Real,
  lt zero a -> lt zero b ->
  sigT
    (fun _ : ubw_b_deslack_principle ->
        le (abs (csm_sumf bool (true :: false :: nil) (ubw_b_mixed_f a b)))
           (csm_sumf bool (true :: false :: nil)
              (fun s : bool => abs (ubw_b_mixed_f a b s))) =>
     sigT (fun _ : lt zero (ubw_b_mixed_f a b true) =>
           lt (ubw_b_mixed_f a b false) zero)).
Proof.
  intros a b Ha Hb.
  exact (existT _
           (fun Hdeslack =>
              ubw_b_deslack_wall bool (true :: false :: nil)
                (ubw_b_mixed_f a b) Hdeslack)
           (existT _ Ha
              (req_lt_id_r_loc (opp b) (opp zero) zero
                 (req_trans (opp zero) (plus zero (opp zero)) zero
                    (req_sym (plus zero (opp zero)) (opp zero)
                       (req_plus_zero_l (opp zero)))
                    (plus_opp zero))
                 (opp_lt_compat zero b Hb)))).
Qed.

(* ============ §4 链身 eps 迭代镜件 + cmk 末端消费定理逐 eps 镜像 ============ *)

Section ChainEpsBody.

(* 链身体：步算子 + TV 泛函抽象位（库内同位 = rsq/k_step 核迭代 +
   tv_req；链身单步收缩的逐 eps 形为诚实证书槽，见文件头申报） *)
Variable S : Set.
Variable tvr : (S -> Real) -> (S -> Real) -> Real.
Variable tstep : (S -> Real) -> (S -> Real).
Variable omd : Real.
Variable eps0 : Real.

Hypothesis Homd_pos : lt zero omd.
Hypothesis Homd_lt_one : lt omd one.

(* 链身 eps 收缩槽：tv_contraction 链身层的逐 eps 形——
   槽位假设面与库内 cmk_* 消费 rsq_bounded_softmax_tv_iter 的假设位同构 *)
Hypothesis Hstep_eps : forall mu nu : S -> Real,
  le (tvr (tstep mu) (tstep nu)) (plus (mult omd (tvr mu nu)) eps0).

(* 余量系数：c_0 = 0，c_{n+1} = 1 + omd·c_n——递推精确闭合，
   无几何级数 bounding 冒充 *)
Fixpoint ubw_b_cslack (n : nat) : Real :=
  match n with
  | 0%nat => zero
  | Datatypes.S m => plus one (mult omd (ubw_b_cslack m))
  end.

(* 链步迭代（rsq_u_titer / k_titer / cmk_titer 同形） *)
Fixpoint ubw_b_titer (n : nat) (mu : S -> Real) : S -> Real :=
  match n with
  | 0%nat => mu
  | Datatypes.S m => tstep (ubw_b_titer m mu)
  end.

(* 4a 链身 eps 迭代镜件：n 步后 TV ≤ omd^n·TV₀ + c_n·eps₀（精确余量递推）。
   底 case req 数乘单位换轨；递归步 = 槽位一次 + IH 经 omd 数乘抬升
   （req_le_mult_compat_r）+ 同右端加项保序（ubw_b_le_plus_r）+
   分配/结合/交换 req 链闭合 c_{n+1} 递推形。 *)
Theorem ubw_b_chain_eps_iter : forall (n : nat) (mu nu : S -> Real),
  le (tvr (ubw_b_titer n mu) (ubw_b_titer n nu))
     (plus (mult (req_r_pow omd n) (tvr mu nu))
           (mult (ubw_b_cslack n) eps0)).
Proof.
  intro n. induction n as [| n IH]; intros mu nu.
  - (* 底：omd^0 ≡ one、c_0 ≡ zero，req 链归一回 TV₀ 本体 *)
    exact (le_trans (tvr mu nu) (mult one (tvr mu nu))
             (plus (mult (req_r_pow omd 0%nat) (tvr mu nu))
                   (mult (ubw_b_cslack 0%nat) eps0))
             (le_id_r (tvr mu nu) (tvr mu nu) (mult one (tvr mu nu))
                (req_sym (mult one (tvr mu nu)) (tvr mu nu)
                   (req_mult_one_l (tvr mu nu)))
                (le_refl (tvr mu nu)))
             (le_id_r (mult one (tvr mu nu))
                (plus (mult one (tvr mu nu)) zero)
                (plus (mult (req_r_pow omd 0%nat) (tvr mu nu))
                      (mult (ubw_b_cslack 0%nat) eps0))
                (req_trans (plus (mult one (tvr mu nu)) zero)
                   (plus (mult one (tvr mu nu)) (mult zero eps0))
                   (plus (mult (req_r_pow omd 0%nat) (tvr mu nu))
                         (mult (ubw_b_cslack 0%nat) eps0))
                   (req_plus_compat (mult one (tvr mu nu))
                      (mult one (tvr mu nu))
                      zero (mult zero eps0)
                      (req_refl (mult one (tvr mu nu)))
                      (req_sym (mult zero eps0) zero
                         (req_trans (mult zero eps0) (mult eps0 zero) zero
                            (mult_comm zero eps0) (mult_zero eps0))))
                   (req_refl (plus (mult (req_r_pow omd 0%nat) (tvr mu nu))
                              (mult (ubw_b_cslack 0%nat) eps0))))
                (req_le_plus_nonneg_r (mult one (tvr mu nu)) zero
                   (le_refl zero)))).
  - (* 递归步 *)
    assert (Homd_le0 : le zero omd) by exact (lt_le_iff zero omd (inl Homd_pos)).
    apply (le_trans
             (tvr (ubw_b_titer (Datatypes.S n) mu)
                  (ubw_b_titer (Datatypes.S n) nu))
             (plus (mult omd (tvr (ubw_b_titer n mu) (ubw_b_titer n nu))) eps0)
             (plus (mult (req_r_pow omd (Datatypes.S n)) (tvr mu nu))
                   (mult (ubw_b_cslack (Datatypes.S n)) eps0))).
    + (* 槽位一次（链身单步 eps 收缩） *)
      exact (Hstep_eps (ubw_b_titer n mu) (ubw_b_titer n nu)).
    + (* omd 数乘抬升 IH，再同右端加 eps0 *)
      apply (le_trans
               (plus (mult omd (tvr (ubw_b_titer n mu) (ubw_b_titer n nu))) eps0)
               (plus (mult omd (plus (mult (req_r_pow omd n) (tvr mu nu))
                              (mult (ubw_b_cslack n) eps0)))
                     eps0)
               (plus (mult (req_r_pow omd (Datatypes.S n)) (tvr mu nu))
                     (mult (ubw_b_cslack (Datatypes.S n)) eps0))).
      * exact (ubw_b_le_plus_r
                 (mult omd (tvr (ubw_b_titer n mu) (ubw_b_titer n nu)))
                 (mult omd (plus (mult (req_r_pow omd n) (tvr mu nu))
                                 (mult (ubw_b_cslack n) eps0)))
                 eps0
                 (req_le_mult_compat_r omd
                    (tvr (ubw_b_titer n mu) (ubw_b_titer n nu))
                    (plus (mult (req_r_pow omd n) (tvr mu nu))
                          (mult (ubw_b_cslack n) eps0))
                    Homd_le0 (IH mu nu))).
      * (* req 链（平化三段）：MID2 →(distrib)→ (A+T)+eps0 →(assoc 对称)→
              A+(T+eps0) →(mult_assoc+尾链)→ RHS；le_id_r+le_refl 升格为 le *)
        exact (ubw_b_req_le
                 (plus (mult omd (plus (mult (req_r_pow omd n) (tvr mu nu))
                                (mult (ubw_b_cslack n) eps0)))
                       eps0)
                 (plus (mult (req_r_pow omd (Datatypes.S n)) (tvr mu nu))
                       (mult (ubw_b_cslack (Datatypes.S n)) eps0))
                 (req_trans
                    (plus (mult omd (plus (mult (req_r_pow omd n) (tvr mu nu))
                                   (mult (ubw_b_cslack n) eps0)))
                          eps0)
                    (plus (plus (mult omd (mult (req_r_pow omd n) (tvr mu nu)))
                           (mult omd (mult (ubw_b_cslack n) eps0)))
                          eps0)
                    (plus (mult (req_r_pow omd (Datatypes.S n)) (tvr mu nu))
                          (mult (ubw_b_cslack (Datatypes.S n)) eps0))
                    (req_plus_compat
                       (mult omd (plus (mult (req_r_pow omd n) (tvr mu nu))
                                (mult (ubw_b_cslack n) eps0)))
                       (plus (mult omd (mult (req_r_pow omd n) (tvr mu nu)))
                          (mult omd (mult (ubw_b_cslack n) eps0)))
                       eps0 eps0
                       (distrib omd (mult (req_r_pow omd n) (tvr mu nu))
                          (mult (ubw_b_cslack n) eps0))
                       (req_refl eps0))
                    (req_trans
                       (plus (plus (mult omd (mult (req_r_pow omd n) (tvr mu nu)))
                              (mult omd (mult (ubw_b_cslack n) eps0)))
                             eps0)
                       (plus (mult omd (mult (req_r_pow omd n) (tvr mu nu)))
                          (plus (mult omd (mult (ubw_b_cslack n) eps0)) eps0))
                       (plus (mult (req_r_pow omd (Datatypes.S n)) (tvr mu nu))
                             (mult (ubw_b_cslack (Datatypes.S n)) eps0))
                       (req_sym
                          (plus (mult omd (mult (req_r_pow omd n) (tvr mu nu)))
                             (plus (mult omd (mult (ubw_b_cslack n) eps0)) eps0))
                          (plus (plus (mult omd (mult (req_r_pow omd n) (tvr mu nu)))
                                   (mult omd (mult (ubw_b_cslack n) eps0)))
                                eps0)
                          (plus_assoc (mult omd (mult (req_r_pow omd n) (tvr mu nu)))
                             (mult omd (mult (ubw_b_cslack n) eps0)) eps0))
                       (req_plus_compat
                          (mult omd (mult (req_r_pow omd n) (tvr mu nu)))
                          (mult (mult omd (req_r_pow omd n)) (tvr mu nu))
                          (plus (mult omd (mult (ubw_b_cslack n) eps0)) eps0)
                          (mult (ubw_b_cslack (Datatypes.S n)) eps0)
                          (mult_assoc omd (req_r_pow omd n) (tvr mu nu))
                          (req_trans
                             (plus (mult omd (mult (ubw_b_cslack n) eps0)) eps0)
                             (plus eps0 (mult omd (mult (ubw_b_cslack n) eps0)))
                             (mult (ubw_b_cslack (Datatypes.S n)) eps0)
                             (plus_comm (mult omd (mult (ubw_b_cslack n) eps0)) eps0)
                             (req_trans
                                (plus eps0 (mult omd (mult (ubw_b_cslack n) eps0)))
                                (plus (mult one eps0)
                                   (mult (mult omd (ubw_b_cslack n)) eps0))
                                (mult (ubw_b_cslack (Datatypes.S n)) eps0)
                                (req_plus_compat eps0 (mult one eps0)
                                   (mult omd (mult (ubw_b_cslack n) eps0))
                                   (mult (mult omd (ubw_b_cslack n)) eps0)
                                   (req_sym (mult one eps0) eps0
                                      (req_trans (mult one eps0)
                                         (mult eps0 one) eps0
                                         (mult_comm one eps0)
                                         (mult_one eps0)))
                                   (mult_assoc omd (ubw_b_cslack n) eps0))
                                (req_sym (mult (ubw_b_cslack (Datatypes.S n)) eps0)
                                   (plus (mult one eps0)
                                      (mult (mult omd (ubw_b_cslack n)) eps0))
                                   (ubw_b_mult_plus_distr_l one
                                      (mult omd (ubw_b_cslack n)) eps0))))))
        )).
Qed.

(* 4b cmk 末端消费定理逐 eps 镜像·严格版。
   装配结构与 cmk_attention_mixing_time（UpReqConcMixSel.v:856-884）逐位
   同形：k 选择消费库件 cmk_k_select（构造核心直连，首参证书=§1 闭证书），
   req_r_pow/cmk_r_pow 换形镜像母件 :871-878 的同款 req 链
   （cmk_r_pow_req_r_pow + req_mult_compat + lt_id_r）；链身消费取逐 eps 形
   （4a），结论右端携诚实余量 c_k·eps0（le_lt_trans + 同右端加项严格化）。 *)
Theorem ubw_b_cmk_eps_mirror : forall mu nu : S -> Real,
  forall budget : Real,
  lt zero budget ->
  le zero (tvr mu nu) ->
  (forall x : Real, le zero x ->
     sigT (fun N : nat => lt x (cmk_scale (Datatypes.S N) one))) ->
  sigT (fun k : nat =>
    lt (tvr (ubw_b_titer k mu) (ubw_b_titer k nu))
       (plus budget (mult (ubw_b_cslack k) eps0))).
Proof.
  intros mu nu budget Hbudget Htv0 Harch.
  destruct (cmk_k_select ubw_b_lt_plus_compat_lt_le omd (tvr mu nu) budget
             Homd_pos Homd_lt_one Htv0 Hbudget Harch) as [k Hk].
  assert (Hk2 : lt (mult (req_r_pow omd k) (tvr mu nu)) budget).
  { exact (lt_id_l (mult (req_r_pow omd k) (tvr mu nu))
                   (mult (cmk_r_pow omd k) (tvr mu nu)) budget
                   (req_mult_compat (req_r_pow omd k) (cmk_r_pow omd k)
                      (tvr mu nu) (tvr mu nu)
                      (req_sym (cmk_r_pow omd k) (req_r_pow omd k)
                         (cmk_r_pow_req_r_pow omd k))
                      (req_refl (tvr mu nu)))
                   Hk). }
  exists k.
  apply (le_lt_trans
           (tvr (ubw_b_titer k mu) (ubw_b_titer k nu))
           (plus (mult (req_r_pow omd k) (tvr mu nu))
                 (mult (ubw_b_cslack k) eps0))
           (plus budget (mult (ubw_b_cslack k) eps0))).
  - exact (ubw_b_chain_eps_iter k mu nu).
  - exact (ubw_b_lt_plus_compat_lt_le
             (mult (req_r_pow omd k) (tvr mu nu)) budget
             (mult (ubw_b_cslack k) eps0) (mult (ubw_b_cslack k) eps0)
             Hk2 (le_refl (mult (ubw_b_cslack k) eps0))).
Qed.

(* 4c cmk 末端消费定理逐 eps 镜像·非严格版（cmk_attention_mixing_time_le
   :887-915 同形；消费 cmk_k_select_le，k 选择换形走 le_id_l 镜像）。 *)
Theorem ubw_b_cmk_eps_mirror_le : forall mu nu : S -> Real,
  forall budget : Real,
  lt zero budget ->
  le zero (tvr mu nu) ->
  (forall x : Real, le zero x ->
     sigT (fun N : nat => lt x (cmk_scale (Datatypes.S N) one))) ->
  sigT (fun k : nat =>
    le (tvr (ubw_b_titer k mu) (ubw_b_titer k nu))
       (plus budget (mult (ubw_b_cslack k) eps0))).
Proof.
  intros mu nu budget Hbudget Htv0 Harch.
  destruct (cmk_k_select_le ubw_b_lt_plus_compat_lt_le omd (tvr mu nu) budget
             Homd_pos Homd_lt_one Htv0 Hbudget Harch) as [k Hk].
  assert (Hk2 : le (mult (req_r_pow omd k) (tvr mu nu)) budget).
  { exact (le_id_l (mult (req_r_pow omd k) (tvr mu nu))
                   (mult (cmk_r_pow omd k) (tvr mu nu)) budget
                   (req_mult_compat (req_r_pow omd k) (cmk_r_pow omd k)
                      (tvr mu nu) (tvr mu nu)
                      (req_sym (cmk_r_pow omd k) (req_r_pow omd k)
                         (cmk_r_pow_req_r_pow omd k))
                      (req_refl (tvr mu nu)))
                   Hk). }
  exists k.
  apply (le_trans
           (tvr (ubw_b_titer k mu) (ubw_b_titer k nu))
           (plus (mult (req_r_pow omd k) (tvr mu nu))
                 (mult (ubw_b_cslack k) eps0))
           (plus budget (mult (ubw_b_cslack k) eps0))).
  - exact (ubw_b_chain_eps_iter k mu nu).
  - exact (ubw_b_le_plus_r (mult (req_r_pow omd k) (tvr mu nu)) budget
             (mult (ubw_b_cslack k) eps0) Hk2).
Qed.

End ChainEpsBody.

(* ============ 审计收尾段（逐件封闭判读，节外全显） ============ *)
Print Assumptions ubw_b_lt_plus_compat_lt_le.
Print Assumptions ubw_b_mult_plus_distr_l.
Print Assumptions ubw_b_le_plus_r.
Print Assumptions ubw_b_plain_upgrade_eps.
Print Assumptions ubw_b_deslack_wall.
Print Assumptions ubw_b_twopt_mixed_sign.
Print Assumptions ubw_b_death_certificate.
Print Assumptions ubw_b_chain_eps_iter.
Print Assumptions ubw_b_cmk_eps_mirror.
Print Assumptions ubw_b_cmk_eps_mirror_le.
