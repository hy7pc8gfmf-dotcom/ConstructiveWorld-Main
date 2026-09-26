(* ============================================================ *)
(* UpAblP7_WallEpsChain_B.v —— 论文7 收缩链链身逐 eps 化件：边界见证与迭代副本。   *)
(*                                                              *)
(* ①使命：本件形式化 W1 链身 eps 化的完成度边界与链身副本组：余量消除论证原理     *)
(*   ⟹ plain 形不可证结果的否定性见证（3b/3d）、逐 eps 迭代副本（余量系数        *)
(*   c_{n+1}=1+omd·c_n 精确递推，4a）、cmk 末端依存定理逐 eps 副本（4b 严格/      *)
(*   4c 非严格）。                                                              *)
(* ②依赖：Stdlib List、CW_ConstructiveWorld_219、UpReqAlgebra、UpReqSumD、        *)
(*   UpReqConcSoftmax、UpReqSampling、UpReqConcMixSel；供给段另引 UpReqConcFin2。 *)
(* ③对标：Doeblin 收缩链逐 eps 混合时间论证的构造性直构（无对应直引）。           *)
(* ④构造性注记：全件语句集合值面；零承认、零经典逻辑捷径、零排中律；              *)
(*   文尾逐件 Print Assumptions 假设审计封闭。                                   *)
(* ⑤编译配方：Rocq 9.1 coqc 直调，cpu_guard 包裹，-o 输出临时目录，树内零写入。   *)
(*                                                              *)
(* 面外扩展标注：本件为工单面外扩展件，按 b3 §2.2 可消解判定施工，候合并方        *)
(*   甄别确认；若属已补强保留区请退回。既往工程自述核实：有——原件头注含既往       *)
(*   工程分级申报（N1/N2/N3）与「Hstep_eps 链身单步收缩逐 eps 形系诚实证书位、     *)
(*   属终装 S8 范畴未开工」自述；此次差异加倍标注：此次按 b3 §2.2 判定            *)
(*   Homd_pos/Homd_lt_one/Hstep_eps 三位为抽象层假设身份保持、实例层可消解，      *)
(*   尾段供给段以 cf2 实例给出三份供给证书（cf2_omd_pos 直引；                    *)
(*   cf2_aux_ds_omd 与 cf2_ds_pos 严格加法换形链；cf2_tv_contraction_eps 直引），  *)
(*   并以 sigT 封装成组（ubw_b_cf2_certs）；抽象参数位（S/tvr/tstep/omd/eps0）    *)
(*   与三假设声明零改，原有证明体零改动。                                        *)
(* ============================================================ *)
From Stdlib Require Import List.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqAlgebra.
Require Import UpReqSumD.
Require Import UpReqConcSoftmax.
Require Import UpReqSampling.
Require Import UpReqConcMixSel.
Import RealInterfaceEnhancedMod.

(* ============ §1 混合加法保序证书件（cmk 选择器首参接口参数闭证书） ============ *)

(* lt a b -> le c d -> lt (a+c) (b+d)。
   依存申报：S07:6118 real_lt_plus_compat_lt_le 具体层成品直闭
   （ConcMixSelFeed.v:112 同款实例化；接口 lt/le 经 RealEnhancedReal 实例
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
   plain 不可证结果注记（UpReqConcSoftmax.v:11-16 已证结论）中的混合号形状 *)
Definition ubw_b_mixed_f (a b : Real) : bool -> Real :=
  fun s : bool => if s then a else opp b.

(* 左分配律辅件：接口 distrib 字段为右分配形，左形经交换律衔接（req 链四段） *)
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
   Or 两支分案（le 定义性 = Or lt req，检验实测双向零摩擦）：
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
   与 3b 否定性见证构成边界两侧：升级方向免费，余量消除论证方向=不可证结果。 *)
Lemma ubw_b_plain_upgrade_eps : forall X Y eps : Real,
  le X Y -> lt zero eps -> le X (plus Y eps).
Proof.
  intros X Y eps Hle Heps.
  exact (le_trans X (plus X zero) (plus Y eps)
           (req_le_plus_nonneg_r X zero (le_refl zero))
           (le_plus_compat X Y zero eps Hle (lt_le_iff zero eps (inl Heps)))).
Qed.

(* 余量消除论证原理（边界对象，仅以类型位出现，本件零假设它成立）：
   逐 eps 上界族闭合到 plain 上界。 *)
Definition ubw_b_deslack_principle : Set :=
  forall X Y : Real,
    (forall eps : Real, lt zero eps -> le X (plus Y eps)) -> le X Y.

(* 3b 否定性见证一般形：余量消除论证原理 ⟹ plain 不可证结果。
   csm 逐 eps 三角（免费档）正是不可证结果 plain 形的逐 eps 逼近像：
   余量消除论证买下的恰是不可证结果本体——链身 eps 化的完成度边界=不可证结果。 *)
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

(* 3c 混合号锚：两点载体上正负支逐点已证结论（sigT 封装防宇宙坑——
   Set 值面合取走依存对，依存对封装同族形） *)
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

(* 3d 否定性见证封装件（cb2w_death_certificate 同范式）：
   「余量消除论证原理在混合号载体上买下 plain 不可证结果实例」×「载体确为混合号」
   双证 sigT 封装——链身 eps 化完成度边界的定理化固化。 *)
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

(* ============ §4 链身 eps 迭代副本件 + cmk 末端依存定理逐 eps 副本 ============ *)

Section ChainEpsBody.

(* 链身体：步算子 + TV 泛函抽象位（库内同位 = rsq/k_step 核迭代 +
   tv_req；链身单步收缩的逐 eps 形为诚实证书参数位，见文件头申报） *)
Variable S : Set.
Variable tvr : (S -> Real) -> (S -> Real) -> Real.
Variable tstep : (S -> Real) -> (S -> Real).
Variable omd : Real.
Variable eps0 : Real.

Hypothesis Homd_pos : lt zero omd.
Hypothesis Homd_lt_one : lt omd one.

(* 链身 eps 收缩参数位：tv_contraction 链身层的逐 eps 形——
   接口参数假设面与库内 cmk_* 依存 rsq_bounded_softmax_tv_iter 的假设位同构 *)
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

(* 4a 链身 eps 迭代副本件：n 步后 TV ≤ omd^n·TV₀ + c_n·eps₀（精确余量递推）。
   底 case req 数乘单位换轨；递归步 = 接口参数一次 + IH 经 omd 数乘抬升
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
    + (* 接口参数一次（链身单步 eps 收缩） *)
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

(* 4b cmk 末端依存定理逐 eps 副本·严格版。
   装配结构与 cmk_attention_mixing_time（UpReqConcMixSel.v:856-884）逐位
   同形：k 选择依存库件 cmk_k_select（构造核心直连，首参证书=§1 闭证书），
   req_r_pow/cmk_r_pow 换形副本源模块 :871-878 的同款 req 链
   （cmk_r_pow_req_r_pow + req_mult_compat + lt_id_r）；链身依存取逐 eps 形
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

(* 4c cmk 末端依存定理逐 eps 副本·非严格版（cmk_attention_mixing_time_le
   :887-915 同形；依存 cmk_k_select_le，k 选择换形走 le_id_l 副本）。 *)
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
Print Assumptions ubw_b_req_le.

(* ============================================================ *)
(* 供给段（签名保持式消解，b3 §2.2.1；原节声明与三假设声明零改）：                *)
(*   链身三证书位在 cf2 实例（UpReqConcFin2 两点有界 softmax 具体层）上供给：      *)
(*   Homd_pos 位引 cf2_omd_pos；Homd_lt_one 位由 cf2_aux_ds_omd 与 cf2_ds_pos     *)
(*   经严格加法保序及右端 req 换形链导出；Hstep_eps 位引 cf2_tv_contraction_eps    *)
(*   （带两侧分布归一前提的逐 eps 单步收缩，余量参数全称量化，强于固定余量的      *)
(*   原假设形）。抽象层三位保持假设身份，本段为具体实例上的消解证书，              *)
(*   并以 sigT 封装成组供下游整取。                                              *)
(* ============================================================ *)
Require Import UpReqConcFin2.

Theorem ubw_b_omd_pos_supply : lt zero cf2_omd.
Proof.
  exact cf2_omd_pos.
Qed.

Theorem ubw_b_omd_lt_one_supply : lt cf2_omd one.
Proof.
  exact (lt_id_r cf2_omd (plus cf2_delta_star cf2_omd) one
           cf2_aux_ds_omd
           (lt_id_l cf2_omd (plus zero cf2_omd)
              (plus cf2_delta_star cf2_omd)
              (req_sym (plus zero cf2_omd) cf2_omd (req_plus_zero_l cf2_omd))
              (ubw_b_lt_plus_compat_lt_le zero cf2_delta_star cf2_omd cf2_omd
                 cf2_ds_pos (le_refl cf2_omd)))).
Qed.

Theorem ubw_b_step_eps_supply :
  forall (mu nu : bool -> Real) (eps : Real),
    req (cf2_sumf mu) one -> req (cf2_sumf nu) one -> lt zero eps ->
    le (cf2_tv (cf2_k_step mu) (cf2_k_step nu))
       (plus (mult cf2_omd (cf2_tv mu nu)) eps).
Proof.
  exact cf2_tv_contraction_eps.
Qed.

Theorem ubw_b_cf2_certs :
  sigT (fun _ : lt zero cf2_omd =>
        sigT (fun _ : lt cf2_omd one =>
              forall (mu nu : bool -> Real) (eps : Real),
                req (cf2_sumf mu) one -> req (cf2_sumf nu) one ->
                lt zero eps ->
                le (cf2_tv (cf2_k_step mu) (cf2_k_step nu))
                   (plus (mult cf2_omd (cf2_tv mu nu)) eps))).
Proof.
  exact (existT _ ubw_b_omd_pos_supply
           (existT _ ubw_b_omd_lt_one_supply ubw_b_step_eps_supply)).
Qed.

(* ---- 供给段假设审计（四连 Print Assumptions） ---- *)
Print Assumptions ubw_b_omd_pos_supply.
Print Assumptions ubw_b_omd_lt_one_supply.
Print Assumptions ubw_b_step_eps_supply.
Print Assumptions ubw_b_cf2_certs.
