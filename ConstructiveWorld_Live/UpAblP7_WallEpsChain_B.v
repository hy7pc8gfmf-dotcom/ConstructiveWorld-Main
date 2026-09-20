(* ============================================================ *)
(* UpAblP7_WallEpsChain_B.v —— 链式迭代的逐 eps 收敛定理与混合时间定理的逐 eps 形 *)
(*                                                              *)
(* 数学使命：本件形式化单步收缩常数 omd（0 < omd < 1）下链式迭代的逐 eps 余量    *)
(*   定理 ubw_b_chain_eps_iter：n 步迭代后                                       *)
(*   TV ≤ omd^n·TV₀ + c_n·eps0，其中余量系数 c_0 = 0、c_{n+1} = 1 + omd·c_n      *)
(*   精确递推闭合；并给出混合时间定理（cmk_attention_mixing_time 与              *)
(*   cmk_attention_mixing_time_le）的逐 eps 形：存在 k 使                        *)
(*   TV ≤ budget + c_k·eps0（非严格形）/ TV < budget + c_k·eps0（严格形）。      *)
(*                                                              *)
(* 边界结果：升级方向 ubw_b_plain_upgrade_eps 直接构造（不带余量上界 ⟹           *)
(*   对一切 eps>0 的逐 eps 上界）；反向 ubw_b_deslack_wall 表明：余量消除原理      *)
(*   ubw_b_deslack_principle 蕴含绝对值三角不等式的不带余量形。两侧共同          *)
(*   定位不带余量形与逐 eps 形之间的边界。                                       *)
(*                                                              *)
(* 附属结果：两点变号载体 ubw_b_mixed_f 上的符号合取见证                         *)
(*   ubw_b_twopt_mixed_sign，及其与余量消除原理实例的合取见证                      *)
(*   ubw_b_death_certificate。                                                  *)
(*                                                              *)
(* 依赖清单：CW_ConstructiveWorld_219、UpReqAlgebra、UpReqSumD、                 *)
(*   UpReqConcSoftmax（提供逐 eps 三角不等式 csm_abs_sum_le_eps）、              *)
(*   UpReqSampling、UpReqConcMixSel（提供 cmk_k_select 与 cmk_k_select_le）；     *)
(*   实数接口取 RealEnhancedReal 具体层实例（导入后裸名同源同解析）。            *)
(*                                                              *)
(* 证明要点：§1 混合加法保序由具体层成品 real_lt_plus_compat_lt_le 闭合          *)
(*   （该命题在抽象层不可由接口字段导出）；§2 辅件经 mult_comm、distrib、        *)
(*   req_plus_compat 构造；§3 边界组由 le_trans、req_le_plus_nonneg_r、          *)
(*   le_plus_compat 与 csm_abs_sum_le_eps 的实例化构成；§4 对 n 归纳：           *)
(*   底情形由 req_mult_one_l、mult_zero 归一，归纳步由单步前提 Hstep_eps、       *)
(*   req_le_mult_compat_r 与 ubw_b_le_plus_r 推进，末段以分配/结合/交换律        *)
(*   闭合 c_{n+1} 递推形；末端 k 的选取应用 cmk_k_select / cmk_k_select_le，     *)
(*   幂换形经 cmk_r_pow_req_r_pow、req_mult_compat。                             *)
(*                                                              *)
(* 构造性注记：全件语句集合值面；零承认、零经典逻辑捷径、零排中律；              *)
(*   见证以依存对承载；文尾对逐件 Print Assumptions 审计封闭。                   *)
(*                                                              *)
(* 编译配方：Rocq 9.1 直调、cpu_guard 节流、-o 临时目录输出（树内零写入）。      *)
(*                                                              *)
(* 主要结果一览：                                                               *)
(*   ubw_b_lt_plus_compat_lt_le : lt a b -> le c d -> lt (a+c) (b+d)。          *)
(*   ubw_b_mult_plus_distr_l : 左分配律 req ((a+b)·c) (a·c+b·c)。               *)
(*   ubw_b_le_plus_r : le a b -> le (plus a c) (plus b c)。                     *)
(*   ubw_b_req_le : req a b -> le a b。                                         *)
(*   ubw_b_plain_upgrade_eps : le X Y -> lt zero eps -> le X (plus Y eps)。     *)
(*   ubw_b_deslack_principle : 余量消除原理的类型定义（Set 层边界对象）。          *)
(*   ubw_b_deslack_wall : 余量消除原理 ⟹ |Σ f(s)| ≤ Σ |f(s)|（csm_sumf 上）。     *)
(*   ubw_b_twopt_mixed_sign : 变号载体上两肢符号性的合取见证。                   *)
(*   ubw_b_death_certificate : 余量消除原理实例与载体符号性的合取见证。            *)
(*   ubw_b_chain_eps_iter : 链式迭代主不等式（见使命行）。                       *)
(*   ubw_b_cmk_eps_mirror / ubw_b_cmk_eps_mirror_le : 混合时间定理的逐 eps 形。  *)
(*                                                              *)
(* 单步前提 Hstep_eps 的地位：本件在 Section 内以其为假设；由链根的逐 eps 形     *)
(*   重推它需先建立 rsq_u_tv_contraction 的长 req 链，属后续工作；其假设面       *)
(*   与库内 cmk_attention_mixing_time 应用 rsq_bounded_softmax_tv_iter 处        *)
(*   的前提同构，未见削弱。                                                      *)
(* ============================================================ *)

From Stdlib Require Import List.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqSumD.
Require Import UpReqConcSoftmax.
Require Import UpReqSampling.
Require Import UpReqConcMixSel.
Import RealInterfaceEnhancedMod.

(* ============ §1 混合加法保序（cmk_k_select 首参证明） ============ *)

(* lt a b -> le c d -> lt (a+c) (b+d)。
   由具体层 real_lt_plus_compat_lt_le 直接闭合；接口 lt/le 经
   RealEnhancedReal 实例与 real_lt/real_le 同源同解析。该命题在抽象层
   不可由接口字段导出（UpReqAlgebra 的 ReqStrictOrderBridge 对此有
   相应注记）；本件在具体实例层给出证明，零承认；该结果随后作为
   cmk_k_select 与 cmk_k_select_le 的首参证明使用。 *)
Theorem ubw_b_lt_plus_compat_lt_le : forall a b c d : Real,
  lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  exact real_lt_plus_compat_lt_le.
Qed.

(* ============ §2 加法保序与左分配律辅件 ============ *)

(* 两点变号载体：true ↦ a（正），false ↦ −b——其上 Σ f = a − b 而
   Σ|f| = a + b，三角不等式在此载体上取严格形。 *)
Definition ubw_b_mixed_f (a b : Real) : bool -> Real :=
  fun s : bool => if s then a else opp b.

(* 左分配律：接口 distrib 字段为右分配形；左形经 mult_comm、distrib 与 req_plus_compat 推得 *)
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
   对 le 的定义性 Or 分情形：lt 支由 ubw_b_lt_plus_compat_lt_le，
   req 支由 req_plus_compat 与 le_id_r。 *)
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

(* req 升格引理：req a b ⟹ le a b（由 lt_le_iff 的 inr 支直接构造） *)
Lemma ubw_b_req_le : forall a b : Real,
  req a b -> le a b.
Proof.
  intros a b Hreq.
  exact (lt_le_iff a b (inr Hreq)).
Qed.

(* ============ §3 不带余量形与逐 eps 形的边界 ============ *)

(* 3a 升级方向边界引理：不带余量上界 ⟹ 逐 eps 上界（可构造方向）。
   与 3b（ubw_b_deslack_wall）构成边界两侧：升级方向直接构造，反向需余量消除原理。 *)
Lemma ubw_b_plain_upgrade_eps : forall X Y eps : Real,
  le X Y -> lt zero eps -> le X (plus Y eps).
Proof.
  intros X Y eps Hle Heps.
  exact (le_trans X (plus X zero) (plus Y eps)
           (req_le_plus_nonneg_r X zero (le_refl zero))
           (le_plus_compat X Y zero eps Hle (lt_le_iff zero eps (inl Heps)))).
Qed.

(* 余量消除原理（ubw_b_deslack_principle）：对一切 eps>0 有 X ≤ Y+eps 则 X ≤ Y。
   本件仅以其类型为边界对象，不假设其成立。 *)
Definition ubw_b_deslack_principle : Set :=
  forall X Y : Real,
    (forall eps : Real, lt zero eps -> le X (plus Y eps)) -> le X Y.

(* 3b 归约：余量消除原理 ⟹ 三角不等式（不带余量形）。
   逐 eps 三角不等式 csm_abs_sum_le_eps 是不带余量形的逐 eps 逼近：
   由余量消除原理恰得三角不等式本体。 *)
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

(* 3c 变号载体上的符号合取：lt zero (f true) 与 lt (f false) zero 两肢
   逐点成立；Set 值面的合取以 sigT 依存对承载。 *)
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

(* 3d 合取见证：「余量消除原理蕴含两点载体上的三角不等式实例」与
   「载体的符号性（ubw_b_twopt_mixed_sign）」两个见证以 sigT 依存对
   一并给出，定理化边界位置。 *)
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

(* ============ §4 链式迭代的逐 eps 定理与混合时间定理的逐 eps 形 ============ *)

Section ChainEpsBody.

(* Section 体：步算子 tstep 与 TV 泛函 tvr 的抽象（与库内 rsq_u_titer 同形）；
   单步收缩的逐 eps 形以假设 Hstep_eps 给出，其地位见文件头。 *)
Variable S : Set.
Variable tvr : (S -> Real) -> (S -> Real) -> Real.
Variable tstep : (S -> Real) -> (S -> Real).
Variable omd : Real.
Variable eps0 : Real.

Hypothesis Homd_pos : lt zero omd.
Hypothesis Homd_lt_one : lt omd one.

(* 单步收缩的逐 eps 前提：对应 rsq_u_tv_contraction 中间层的逐 eps 形；
   假设面与库内 cmk_attention_mixing_time 应用 rsq_bounded_softmax_tv_iter 处同构 *)
Hypothesis Hstep_eps : forall mu nu : S -> Real,
  le (tvr (tstep mu) (tstep nu)) (plus (mult omd (tvr mu nu)) eps0).

(* 余量系数：c_0 = 0，c_{n+1} = 1 + omd·c_n——递推精确闭合，
   非几何级数放缩所得的粗界 *)
Fixpoint ubw_b_cslack (n : nat) : Real :=
  match n with
  | 0%nat => zero
  | Datatypes.S m => plus one (mult omd (ubw_b_cslack m))
  end.

(* 链步迭代：n 次复合 tstep（n = 0 时为恒等；与库内 rsq_u_titer 同形） *)
Fixpoint ubw_b_titer (n : nat) (mu : S -> Real) : S -> Real :=
  match n with
  | 0%nat => mu
  | Datatypes.S m => tstep (ubw_b_titer m mu)
  end.

(* 4a 链式迭代主定理：n 步后 TV ≤ omd^n·TV₀ + c_n·eps0（余量系数精确递推）。
   底情形由 req 数乘单位律归一；归纳步：由 n 到 S n——单步前提 Hstep_eps
   应用一次，归纳假设经 req_le_mult_compat_r 以 omd 数乘，再由
   ubw_b_le_plus_r 同右端加项；末段以分配/结合/交换律闭合 c_{n+1} 递推形。 *)
Theorem ubw_b_chain_eps_iter : forall (n : nat) (mu nu : S -> Real),
  le (tvr (ubw_b_titer n mu) (ubw_b_titer n nu))
     (plus (mult (req_r_pow omd n) (tvr mu nu))
           (mult (ubw_b_cslack n) eps0)).
Proof.
  intro n. induction n as [| n IH]; intros mu nu.
  - (* 情形 n=0：omd^0 ≡ one、c_0 ≡ zero，由 req 数乘单位律归一到 TV₀ *)
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
  - (* 情形 n=S n'：归纳步，由 n 到 S n *)
    assert (Homd_le0 : le zero omd) by exact (lt_le_iff zero omd (inl Homd_pos)).
    apply (le_trans
             (tvr (ubw_b_titer (Datatypes.S n) mu)
                  (ubw_b_titer (Datatypes.S n) nu))
             (plus (mult omd (tvr (ubw_b_titer n mu) (ubw_b_titer n nu))) eps0)
             (plus (mult (req_r_pow omd (Datatypes.S n)) (tvr mu nu))
                   (mult (ubw_b_cslack (Datatypes.S n)) eps0))).
    + (* 单步前提 Hstep_eps 应用一次（一步收缩的逐 eps 形） *)
      exact (Hstep_eps (ubw_b_titer n mu) (ubw_b_titer n nu)).
    + (* 归纳假设以 omd 数乘（req_le_mult_compat_r），再同右端加 eps0 *)
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
      * (* req 传递链三段：distrib 展开加法，plus_assoc 重排结合，mult_assoc、
              mult_comm、plus_comm 与 ubw_b_mult_plus_distr_l 收尾至右端；req 经 ubw_b_req_le 升格为 le *)
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

(* 4b 混合时间定理的逐 eps 形·严格版。
   陈述与 cmk_attention_mixing_time（UpReqConcMixSel）同构：k 的选取由
   库件 cmk_k_select 给出（首参证明即 §1 的 ubw_b_lt_plus_compat_lt_le）；
   幂换形经 cmk_r_pow_req_r_pow、req_mult_compat 与 lt_id_r；
   链上不等式取 4a 的逐 eps 形（ubw_b_chain_eps_iter），结论右端携
   余量 c_k·eps0（le_lt_trans 与同右端加项严格化）。 *)
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

(* 4c 混合时间定理的逐 eps 形·非严格版（与 cmk_attention_mixing_time_le
   同构；k 的选取由 cmk_k_select_le 给出，幂换形经 le_id_l）。 *)
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

(* ============ 假设审计（对逐件 Print Assumptions） ============ *)
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
