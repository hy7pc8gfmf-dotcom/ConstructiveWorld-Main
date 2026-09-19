(* ============================================================ *)
(* UpAblAlmConsumption.v —— Z1b 席：alm 链余前件形消费示范件        *)
(* （ConstructiveWorld 消融战役，20260920；零承认件；纯构造性）      *)
(*                                                              *)
(* 使命：在自建并列双 max 最小世界（二元词表 [true; false]，        *)
(*   logit 常值——并列副本世界的最小模型），只消费已注册链件         *)
(*   （UpReqAttnQ18Tail 的 aqt_T0_mass_rest / aqt_T0_l1 两件出节     *)
(*   定理，即上游 UpReqAttnMassSplit 的 ams_mass_rest_le /          *)
(*   ams_l1_le 在 T₀=299/1000 载体与 UpReqAttnUniformLimit 的       *)
(*   alm_invk / alm_uniform 定义面），装配「并列副本情形             *)
(*   TV(w_T, δ_uniform) ≤ eps 分解上界链」的 alm 主槽余前件形实例。  *)
(*                                                              *)
(* 诚实定性（禁虚报）：这是「alm 主槽闭合前的结构承载验证」，        *)
(*   非本体闭合——主件 alm_uniform_limit 陈述已在上游头注冻结         *)
(*   （∀eps>0, sigT T₀(>0) ∧ ∀T<T₀, L1(w_T,u) ≤ eps；本体闭合归      *)
(*   Z1a 席，本席禁触该件）。本件把主槽在 T₀ 载体温度的实例          *)
(*   （L1 ≤ k·eps）以显式前提保留（余前件形，照 X2 tx2_ppo66 条件形   *)
(*   范式），分解结构完整可验：                                     *)
(*     TV := (1/k)·L1（alm_invk 并列实例=半和因子）                 *)
(*     消费位①：aqt_T0_mass_rest——非 m 质量 M ≤ n·decay_T₀         *)
(*     消费位②：aqt_T0_l1——L1 ≤ n·decay_T₀ + n·decay_T₀            *)
(*     余前件位：(n·decay + n·decay) ≤ k·eps —— γ=0 档 decay 不      *)
(*       趋于 0（并列副本=一致间隙前提未覆盖面），此位即主槽         *)
(*       闭合缺口，显式保留；接通后 TV ≤ eps 一跳即达。              *)
(*                                                              *)
(* 并列世界数据证书：tie（双 max 同值）+ gap0（γ:=0 非严格档         *)
(*   的一致间隙前提真实现——并列世界只能满足 γ=0 档；严格档 γ>0        *)
(*   被并列证书驳回，这正是链件 l1_le/mass_rest_le 在此只能以        *)
(*   余前件形承载的原因）。                                         *)
(*                                                              *)
(* 纪律：语句面全 Set 层（real_lt 为见证和形、real_le/real_eq 为     *)
(*   S01/S07 可解码面；零裸命题层泄露、零假设声明位）；全 Qed；        *)
(*   前缀 almc_（全库实扫零撞名）；上游零改；未入 order.txt/         *)
(*   _CoqProject。                                                  *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S07_RealSetoidExpLog.
Require Import CW_ConstructiveWorld_219.
Require Import AttnHardLimit218.
Require Import UpReqAttnUniformLimit.
Require Import UpReqAttnMassSplit.
Require Import UpReqAttnQ18Tail.
From Stdlib Require Import List Arith.

(* ############ 并列双 max 最小世界（二元词表 flag 载体） ############ *)

(* 词汇表：二元词表；logit 常值实一——两 token 并列同为 max。 *)
Definition almc_vocab : list bool := true :: false :: nil.

Definition almc_z : bool -> Real := fun _ => real_one.

(* 并列证书：双 max 同值（z 常值，定义形） *)
Lemma almc_tie : real_eq (almc_z true) (almc_z false).
Proof. apply real_eq_refl. Qed.

(* 表可判定等词（S01 Id 面，@inl/@inr 构造；异 constructor 支以
   J-式依赖返回子句驳回：P(y) 在失配指标取空型、在参数侧取 unit，
   id_refl 支由 tt 满足——Id 消除子的指标失配消解范式）。 *)
Definition almc_eq_dec (a b : bool) : Or (Id a b) (Not (Id a b)).
Proof.
  destruct a as [ | ]; destruct b as [ | ].
  - exact (@inl _ _ (@id_refl bool true)).
  - exact (@inr (Id true false) (Not (Id true false))
             (fun H : Id true false =>
                match H in Id _ y
                  return (match y with false => Empty_set | _ => unit end) with
                | id_refl => tt
                end)).
  - exact (@inr (Id false true) (Not (Id false true))
             (fun H : Id false true =>
                match H in Id _ y
                  return (match y with true => Empty_set | _ => unit end) with
                | id_refl => tt
                end)).
  - exact (@inl _ _ (@id_refl bool false)).
Defined.

(* 表非空证书：[true; false] 异于空表（同上 J-式范式）。 *)
Definition almc_vocab_ne : Not (Id almc_vocab nil) :=
  fun H : Id almc_vocab nil =>
    match H in Id _ y
      return (match y with nil => Empty_set | _ => unit end) with
    | id_refl => tt
    end.

(* 副本代表 m := true 入表。 *)
Definition almc_m_in : InT true almc_vocab :=
  @InT_here bool true (false :: nil).

(* 一致间隙前提在本世界的真实现位：γ := real_zero 非严格档。
   （严格档 γ>0 需 real_plus real_one γ ≤ real_one，与并列证书
   相斥——并列副本=严格间隙前提的未覆盖面，故链件只能以余前件形
   承载；见头注。） *)
Lemma almc_gap0 : forall x : bool, Not (Id x true) ->
  real_le (real_plus (almc_z x) real_zero) (almc_z true).
Proof.
  intros x Hx. destruct x as [ | ].
  - (* x = true：与 Not (Id true true) 相斥 *)
    exact (match Hx (@id_refl bool true) with end).
  - (* x = false：1 + 0 ≤ 1（加零恒等经 eq-le 可解码面） *)
    exact (RealSetoid.real_eq_le (real_plus (almc_z false) real_zero)
             (almc_z true) (real_plus_zero real_one)).
Qed.

(* ############ T₀ 温度载体与链件消费位 ############ *)

(* 温度载体：Q 字面量 T₀ = 299/1000（Q18Tail 注册面） *)
Definition almc_T : Real := aqt_q2r aqt_T0.

(* 正性证书必须透明（Defined 数据面）：它在消费型词项内作为
   real_inv_pos/decay_T/ams_w 的实参出现，Qed 不透明会阻断转换。 *)
Definition almc_Tpos : real_lt real_zero almc_T := aqt_T0_pos.

(* 硬注意力权重与副本均匀目标（并列世界实例） *)
Definition almc_w (x : bool) : Real :=
  ams_w bool almc_vocab almc_vocab_ne almc_z almc_T almc_Tpos x.

Definition almc_u (x : bool) : Real :=
  alm_uniform bool almc_vocab almc_eq_dec true almc_m_in x.

(* L1(w_T₀, δ_u) := Σ_vocab |u − w_T₀|（X2 tv 口径） *)
Definition almc_l1 : Real :=
  real_list_sum bool
    (fun x : bool => real_abs (real_minus_r (almc_u x) (almc_w x)))
    almc_vocab.

(* 非 m 质量 M（上游 ams_M 并列实例） *)
Definition almc_M : Real :=
  ams_M bool almc_vocab almc_vocab_ne almc_eq_dec almc_z true
    almc_T almc_Tpos.

(* γ=0 档衰减因子与词表质量界实（n = 2） *)
Definition almc_decay : Real := decay_T real_zero almc_T almc_Tpos.
Definition almc_n : Real := real_of_nat (length almc_vocab).

(* ---------- 消费位①：mass_rest_le 链件真消费 ----------
   aqt_T0_mass_rest（经 ams_mass_rest_le）以并列世界九参全喂入：
   M ≤ n·decay_T₀。 *)
Theorem almc_M_le_decay :
  real_le almc_M (real_mult almc_n almc_decay).
Proof.
  exact (aqt_T0_mass_rest bool almc_vocab almc_vocab_ne almc_eq_dec
           almc_z true almc_m_in real_zero almc_gap0).
Qed.

(* ---------- 消费位②：l1_le 链件真消费 ----------
   aqt_T0_l1（经 ams_l1_le）同轨全喂入：L1 ≤ n·decay + n·decay。 *)
Theorem almc_l1_le_2nd :
  real_le almc_l1
    (real_plus (real_mult almc_n almc_decay)
               (real_mult almc_n almc_decay)).
Proof.
  exact (aqt_T0_l1 bool almc_vocab almc_vocab_ne almc_eq_dec
           almc_z true almc_m_in real_zero almc_gap0).
Qed.

(* ############ TV 半和因子（alm_invk 并列实例）与副本数 ############ *)

(* 副本数实：k = alm_k = count_token true [true; false]（并列世界
   的副本多重数=2，count_token 真折叠——非平凡计算位） *)
Definition almc_k2 : Real :=
  real_of_nat (alm_k bool almc_vocab almc_eq_dec true).

(* 每副本份：alm_invk 并列实例 = 1/k = 1/2（半和因子）。注：real_eq 为
   sigT 见证和形，n≡k2 的 reflexivity 收口须柯西见证归约，非本件
   承载位，不在此装配；消费链不依赖该重合（n/k 各自独立入场）。 *)
Definition almc_inv2 : Real :=
  alm_invk bool almc_vocab almc_eq_dec true almc_m_in.

Lemma almc_inv2_pos : real_lt real_zero almc_inv2.
Proof.
  exact (real_inv_pos_pos almc_k2
           (alm_k_pos bool almc_vocab almc_eq_dec true almc_m_in)).
Qed.

(* inv 核：k · (1/k) == 1（real_inv_pos_correct 经 alm_invk 展开） *)
Lemma almc_k2_inv2_one : real_eq (real_mult almc_k2 almc_inv2) real_one.
Proof.
  exact (real_inv_pos_correct almc_k2
           (alm_k_pos bool almc_vocab almc_eq_dec true almc_m_in)).
Qed.

(* TV(w_T₀, δ_u) := (1/k)·L1（并列世界 k=2 档即半和形） *)
Definition almc_tv : Real := real_mult almc_l1 almc_inv2.

(* 分解恒等式（定义形锚）：TV == (1/k)·L1 的交换重构 *)
Theorem almc_tv_decomp : real_eq almc_tv (real_mult almc_inv2 almc_l1).
Proof. exact (real_mult_comm almc_l1 almc_inv2). Qed.

(* 缩放消去：((k·eps)·(1/k)) == eps（交换/结合/inv 核/幺元四步，
   消费 almc_k2_inv2_one） *)
Lemma almc_scale_cancel : forall e : Real,
  real_eq (real_mult (real_mult almc_k2 e) almc_inv2) e.
Proof.
  intro e.
  apply (real_eq_trans (real_mult (real_mult almc_k2 e) almc_inv2)
           (real_mult almc_inv2 (real_mult almc_k2 e)) _).
  - apply (real_mult_comm (real_mult almc_k2 e) almc_inv2).
  - apply (real_eq_trans (real_mult almc_inv2 (real_mult almc_k2 e))
             (real_mult (real_mult almc_inv2 almc_k2) e) _).
    + apply (real_mult_assoc almc_inv2 almc_k2 e).
    + apply (real_eq_trans (real_mult (real_mult almc_inv2 almc_k2) e)
               (real_mult real_one e) _).
      * apply (RealSetoid.real_eq_mult_compat
                 (real_mult almc_inv2 almc_k2) e real_one e).
        -- apply (real_eq_trans (real_mult almc_inv2 almc_k2)
                    (real_mult almc_k2 almc_inv2) _).
           ++ apply (real_mult_comm almc_inv2 almc_k2).
           ++ exact almc_k2_inv2_one.
        -- apply real_eq_refl.
      * apply (real_eq_trans (real_mult real_one e)
                 (real_mult e real_one) _).
        -- apply (real_mult_comm real_one e).
        -- apply (real_mult_one e).
Qed.

(* ############ 主件：TV ≤ eps 分解上界链——alm 主槽余前件形 #########
   余前件清单（显式保留，照 X2 tx2_ppo66 条件形范式）：
     ① 主槽位：L1(w_T₀, δ_u) ≤ k·eps —— 主槽 alm_uniform_limit
        （冻结陈述 ∀eps>0, sigT T₀(>0) ∧ ∀T<T₀, L1 ≤ eps）在 T₀
        载体温度的实例；本体闭合归 Z1a 席，本件以显式前提保留。
     ② 数据位：eps > 0（主槽量词面）。
   证明体真实消费：almc_inv2_pos（半和因子正性）+ 主槽前提经
   real_le_mult_compat 乘入半和因子 + almc_scale_cancel 代数收口。 *)
Theorem almc_tv_split : forall eps : Real,
  real_lt real_zero eps ->
  real_le almc_l1 (real_mult almc_k2 eps) ->
  real_le almc_tv eps.
Proof.
  intros eps Heps Hslot. unfold almc_tv.
  apply (RealSetoid.real_le_id_r
           (real_mult almc_l1 almc_inv2)
           (real_mult (real_mult almc_k2 eps) almc_inv2) eps).
  - (* 代数收口：((k·eps)·(1/k)) == eps *)
    exact (almc_scale_cancel eps).
  - (* 半和因子乘入：L1·(1/k) ≤ (k·eps)·(1/k) *)
    exact (real_le_mult_compat almc_l1 (real_mult almc_k2 eps)
             almc_inv2 almc_inv2_pos Hslot).
Qed.

(* ############ 全链装配：衰减界槽接通位（分解上界链） ##############
   链形：L1 ≤ n·decay + n·decay（消费位②）
         ⟹ TV ≤ eps（余前件：n·decay + n·decay ≤ k·eps——γ=0 档
            decay 不趋于 0，此位即主槽闭合缺口，显式保留；
            接通后一跳即达）。
   诚实定性：本件验证「分解结构完整可验」，非本体闭合。 *)
Theorem almc_bound_decomp : forall eps : Real,
  real_lt real_zero eps ->
  real_le (real_plus (real_mult almc_n almc_decay)
                      (real_mult almc_n almc_decay))
          (real_mult almc_k2 eps) ->
  real_le almc_tv eps.
Proof.
  intros eps Heps Hbd.
  apply (almc_tv_split eps Heps).
  apply (real_le_trans almc_l1
           (real_plus (real_mult almc_n almc_decay)
                      (real_mult almc_n almc_decay))
           (real_mult almc_k2 eps)).
  - exact almc_l1_le_2nd.
  - exact Hbd.
Qed.

(* ############ G3：提取验证面（单条命令列全部常量——AB7 卡规避） ## *)
(* 出口=零 magic 数值核（z/温度/衰减/词表质量四实函数）。             *)
(* 诚实口径：世界实例面（almc_w 拖 vocab_nonempty、almc_u/M/l1/tv/    *)
(* inv2 拖 eq_dec）含 Id-依赖消除证书值，提取必出 magic——其可计算核  *)
(* （ams_w/alm_k/alm_uniform/alm_switch/count_token/aqt_q2r）已在上游  *)
(* 以节参参数化形式零 magic 提取（attn_q18tail_q18d.ml/               *)
(* attn_uniformlimit_q18.ml/attn_hardlimit218.ml），本件出口与上游     *)
(* 同则收窄；世界实例面留在理论侧承载。                               *)

From Stdlib Require Import Extraction.
Set Extraction Output Directory "attn/z1bex".
Extraction "almc_consumption"
  almc_z almc_T almc_Tpos almc_decay almc_n.

(* ############ G2：逐件公理面自证（应全为 Closed） ################# *)

Print Assumptions almc_tie.
Print Assumptions almc_gap0.
Print Assumptions almc_Tpos.
Print Assumptions almc_M_le_decay.
Print Assumptions almc_l1_le_2nd.
Print Assumptions almc_inv2_pos.
Print Assumptions almc_k2_inv2_one.
Print Assumptions almc_tv_decomp.
Print Assumptions almc_scale_cancel.
Print Assumptions almc_tv_split.
Print Assumptions almc_bound_decomp.
