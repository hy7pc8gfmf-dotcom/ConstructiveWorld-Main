(* ============================================================ *)
(* UpAblP7_P7FlagshipTail.v —— P7BoundedSoftmaxDeep 出节定理的实例化、        *)
(*   独立重证与求和交换恒等三形。                                            *)
(* 使命：使用源模块 P7BoundedSoftmaxDeep.v 出节面（只读）：将 p7d_one_le_hi_sq   *)
(*   （1≤hi²）与 p7d_factor_over_hi（因子-倒数恒等式）实例化于温度:=1、        *)
(*   利差:=1；给出单例非空两向互证与求和交换恒等的显式全称/载体/单例三形。     *)
(* 本件不依赖、不装设同题异向件 UpAblP7_P7KappaFlagship。                     *)
(*                                                                *)
(* 使用面（上游出口真名）：p7d_one_le_hi_sq、p7d_swap_of_sum_eq_list、        *)
(*   p7d_nR_pos_gives_enum_nonempty、p7d_enum_nonempty_gives_nR_pos、         *)
(*   p7d_factor_over_hi、p7d_lsum_fubini_gen（P7BoundedSoftmaxDeep）；        *)
(*   bs_list_sum、bs_hi_pos、nat_to_R_pos（AttnDoeblin）。                    *)
(*                                                                *)
(* 证明来源分层：①上游直接应用——uaft_one_le_hi_sq_one 经                     *)
(*   p7d_one_le_hi_sq、uaft_factor_over_hi_one 经 p7d_factor_over_hi；        *)
(*   ②独立重证——uaft_one_le_hi_sq_indep 以 lo·hi=one 恒等链（expf_plus、      *)
(*   distrib、plus_comm、plus_opp、mult_zero、expf_zero）与 lo<hi 单调链      *)
(*   （lt_mult_compat、mult_comm、lt_id_l/lt_id_r）自证，不使用源模块           *)
(*   bs_lo_hi_eq／bs_lo_lt_hi 两件；③实例供给——温度:=1、利差:=1               *)
(*   （one_pos＋inv_pos_pos），单例载体 (szero::nil)。                        *)
(* sum_eq_list 数据位说明：SumOver 八字段实例构造不可行（zero_nonneg 全称位    *)
(*   须 enum 满射数据）；故交换恒等取三形：显式全称形（求和实例与规范化        *)
(*   证书升为显式全称前提）、载体恒等形（以 bs_list_sum 折叠为求和载体）、     *)
(*   单例计算形（szero::nil 上定义性归约）。                                  *)
(*                                                                *)
(* κ∈(0,1) 前提形：温度/利差数据对＋两正性证书＋指数字段四件（正性/零点/       *)
(*   加法/严格单调），为 uaft_one_le_hi_sq_one 与                             *)
(*   uaft_factor_over_hi_one 共用的九参前提。                                 *)
(*                                                                *)
(* 依赖清单：S01_BaseRing＋CW_ConstructiveWorld_219＋AttnDoeblin＋            *)
(*   P7BoundedSoftmaxDeep＋Stdlib List——只读使用，原树零改。                  *)
(*                                                                *)
(* 定理面（九件，全 Qed，前缀 uaft_）：                                       *)
(*   uaft_one_le_hi_sq_one —— 1≤hi² 于温度:=1、利差:=1 的实例形；             *)
(*   uaft_one_le_hi_sq_indep —— 同结论独立重证（恒等链＋单调链）；             *)
(*   uaft_factor_over_hi_one —— 因子-倒数恒等式实例形；                       *)
(*   uaft_singleton_nR_pos —— 单例载体 nat_to_R>0 计算形；                    *)
(*   uaft_singleton_nonempty_hand —— 单例非空独立重证；                       *)
(*   uaft_singleton_nonempty_via_mother —— 同命题经 p7d_nR_pos_gives_enum_nonempty 的第二证明（两向互证）； *)
(*   uaft_swap_of_sum_eq_list_explicit／uaft_swap_list_carrier_id／           *)
(*   uaft_swap_singleton_carrier —— 交换恒等三形（显式全称/载体/单例）。       *)
(*                                                                *)
(* 对标：mathlib 有限和交换（Fubini 型）与列表求和的构造性 Set 层对应。        *)
(* 构造性注记：语句面全 Set 层；零承认；全 Qed；可提取。                       *)
(* 编译配方：Rocq 9.1 直调 coqc，cpu_guard 包裹，-o 临时目录。                 *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import CW_ConstructiveWorld_219.
Require Import AttnDoeblin.
Require Import P7BoundedSoftmaxDeep.
From Stdlib Require Import List.

(* ################ 段一：展幅 1≤hi² 与因子-倒数（九参前提节） ################ *)

Section UaftScale.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* uaft_one_le_hi_sq_one：p7d_one_le_hi_sq @ 温度:=1、利差:=1 的实例形       *)
(*   （温度与利差均取 one，one_pos 供两处正性位，invT:=inv_pos one one_pos；  *)
(*   指数族保持抽象——全库无具体实数实例） *)
Theorem uaft_one_le_hi_sq_one :
  forall (expf : R -> R) (expf_pos : forall x : R, lt zero (expf x))
         (expf_zero : Id (expf zero) one)
         (expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b)))
         (expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b)),
  le one (mult (expf (mult (inv_pos one one_pos) one))
               (expf (mult (inv_pos one one_pos) one))).
Proof.
  intros expf expf_pos expf_zero expf_plus expf_mono_lt.
  exact (p7d_one_le_hi_sq one one_pos one one_pos expf expf_pos
           expf_zero expf_plus expf_mono_lt).
Qed.

(* uaft_one_le_hi_sq_indep：与 p7d_one_le_hi_sq 同结论的独立重证——先由      *)
(*   恒等链得 lo·hi=one（expf_plus、distrib、plus_comm、plus_opp、mult_zero、 *)
(*   expf_zero），再经 lo<hi 单调链（lt_mult_compat、mult_comm、lt_id_l）     *)
(*   与 le_mult_compat_r 推出 1≤hi·hi；不使用源模块 bs_lo_hi_eq／bs_lo_lt_hi。 *)
Theorem uaft_one_le_hi_sq_indep :
  forall (temp : R) (temp_pos : lt zero temp) (Delta : R) (Delta_pos : lt zero Delta)
         (expf : R -> R) (expf_pos : forall x : R, lt zero (expf x))
         (expf_zero : Id (expf zero) one)
         (expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b)))
         (expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b)),
  le one (mult (expf (mult (inv_pos temp temp_pos) Delta))
               (expf (mult (inv_pos temp temp_pos) Delta))).
Proof.
  intros temp temp_pos Delta Delta_pos expf expf_pos expf_zero expf_plus expf_mono_lt.
  assert (Hlhi : Id (mult (expf (mult (inv_pos temp temp_pos) (opp Delta)))
                          (expf (mult (inv_pos temp temp_pos) Delta))) one).
  { exact (id_trans (id_sym (expf_plus (mult (inv_pos temp temp_pos) (opp Delta))
                                       (mult (inv_pos temp temp_pos) Delta)))
             (id_trans (id_cong expf (id_sym (distrib (inv_pos temp temp_pos)
                                                     (opp Delta) Delta)))
             (id_trans (id_cong expf (id_cong (fun w : R => mult (inv_pos temp temp_pos) w)
                                    (plus_comm (opp Delta) Delta)))
             (id_trans (id_cong expf (id_cong (fun w : R => mult (inv_pos temp temp_pos) w)
                                    (plus_opp Delta)))
                       (id_trans (id_cong expf (mult_zero (inv_pos temp temp_pos)))
                                 expf_zero))))). }
  assert (Hopplt : lt (opp Delta) Delta).
  { exact (le_lt_trans (opp Delta) zero Delta
             (le_id_r (opp Delta) (opp zero) zero opp_zero_t13
                (opp_le_compat zero Delta (lt_le_iff zero Delta (inl Delta_pos))))
             Delta_pos). }
  assert (Hlohi : lt (expf (mult (inv_pos temp temp_pos) (opp Delta)))
                     (expf (mult (inv_pos temp temp_pos) Delta))).
  { apply (expf_mono_lt (mult (inv_pos temp temp_pos) (opp Delta))
                        (mult (inv_pos temp temp_pos) Delta)).
    exact (lt_id_l (mult (inv_pos temp temp_pos) (opp Delta))
                   (mult (opp Delta) (inv_pos temp temp_pos))
                   (mult (inv_pos temp temp_pos) Delta)
                   (mult_comm (inv_pos temp temp_pos) (opp Delta))
                   (lt_id_r (mult (opp Delta) (inv_pos temp temp_pos))
                            (mult Delta (inv_pos temp temp_pos))
                            (mult (inv_pos temp temp_pos) Delta)
                            (mult_comm Delta (inv_pos temp temp_pos))
                            (lt_mult_compat (opp Delta) Delta
                               (inv_pos temp temp_pos)
                               (inv_pos_pos temp temp_pos) Hopplt))). }
  apply (le_trans _ (mult (expf (mult (inv_pos temp temp_pos) Delta))
                          (expf (mult (inv_pos temp temp_pos) (opp Delta))))).
  - exact (le_id_l one (mult (expf (mult (inv_pos temp temp_pos) Delta))
                             (expf (mult (inv_pos temp temp_pos) (opp Delta))))
             (mult (expf (mult (inv_pos temp temp_pos) Delta))
                   (expf (mult (inv_pos temp temp_pos) (opp Delta))))
             (id_sym (id_trans (mult_comm (expf (mult (inv_pos temp temp_pos) Delta))
                                          (expf (mult (inv_pos temp temp_pos) (opp Delta))))
                               Hlhi))
             (le_refl (mult (expf (mult (inv_pos temp temp_pos) Delta))
                            (expf (mult (inv_pos temp temp_pos) (opp Delta)))))).
  - exact (le_mult_compat_r (expf (mult (inv_pos temp temp_pos) Delta))
               (expf (mult (inv_pos temp temp_pos) (opp Delta)))
               (expf (mult (inv_pos temp temp_pos) Delta))
               (lt_le_iff zero (expf (mult (inv_pos temp temp_pos) Delta))
                          (inl (expf_pos (mult (inv_pos temp temp_pos) Delta))))
               (lt_le_iff (expf (mult (inv_pos temp temp_pos) (opp Delta)))
                          (expf (mult (inv_pos temp temp_pos) Delta))
                          (inl Hlohi))).
Qed.

(* uaft_factor_over_hi_one：p7d_factor_over_hi @ 温度:=1 的实例形——         *)
(*   因子-倒数恒等式 e^{a/T}·(e^{Δ/T})⁻¹ = e^{(a−Δ)/T} 的具体温度形；        *)
(*   hi 正性前提由 bs_hi_pos @ one/one 供给。 *)
Theorem uaft_factor_over_hi_one :
  forall (a b : R) (expf : R -> R)
         (expf_pos : forall x : R, lt zero (expf x))
         (expf_zero : Id (expf zero) one)
         (expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b))),
  Id (mult (expf (mult (inv_pos one one_pos) a))
           (inv_pos (expf (mult (inv_pos one one_pos) one))
                    (AttnDoeblin.bs_hi_pos one one_pos one expf expf_pos)))
     (expf (mult (inv_pos one one_pos) (plus a (opp one)))).
Proof.
  intros a b expf expf_pos expf_zero expf_plus.
  exact (p7d_factor_over_hi one one_pos one a b expf expf_pos expf_zero expf_plus).
Qed.

End UaftScale.

(* ################ 段二：单例非空两向互证（nR>0 与 enum 非空） ############## *)
(* 源模块出节面中反向件 p7d_nR_pos_gives_enum_nonempty 不需求和实例，正向件     *)
(*   p7d_enum_nonempty_gives_nR_pos 须 sel 全称位；本件以单例计算位补具体形。  *)

Section UaftTail.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.

(* uaft_singleton_nR_pos：单例载体 nat_to_R>0——length (s::nil) 定义性归约    *)
(*   为 S (length nil)，与 AttnDoeblin.nat_to_R_pos 全称形直接合一。 *)
Theorem uaft_singleton_nR_pos : forall s : S,
  lt zero (AttnDoeblin.nat_to_R (length (s :: nil))).
Proof.
  intro s.
  exact (AttnDoeblin.nat_to_R_pos (length (nil : list S))).
Qed.

(* uaft_singleton_nonempty_hand：独立重证——由 Id (s::nil) nil 经长度映射     *)
(*   得 Id one zero，与 one_pos 矛盾（经 lt_id_l，收于 lt_irrefl）。 *)
Theorem uaft_singleton_nonempty_hand : forall s : S, Not (Id (s :: nil) nil).
Proof.
  intros s H.
  assert (Hone0 : Id one zero).
  { exact (id_trans (id_sym (plus_zero one))
             (id_cong (fun l : list S => AttnDoeblin.nat_to_R (length l)) H)). }
  exact (lt_irrefl one (lt_id_l one zero one Hone0 one_pos)).
Qed.

(* uaft_singleton_nonempty_via_mother：同命题经                              *)
(*   p7d_nR_pos_gives_enum_nonempty @ 单例载体——与 uaft_singleton_nonempty_hand 互为独立证明。 *)
Theorem uaft_singleton_nonempty_via_mother : forall s : S, Not (Id (s :: nil) nil).
Proof.
  intro s.
  exact (p7d_nR_pos_gives_enum_nonempty (s :: nil)
           (AttnDoeblin.nat_to_R_pos (length (nil : list S)))).
Qed.

End UaftTail.

(* ################ 段三：求和交换恒等三形（显式全称/载体恒等/单例） ######### *)
(* 背景：SumOver 八字段实例构造不可行（zero_nonneg 全称位须 enum 满射数据）；  *)
(*   故对本件交换恒等分三形论证：显式全称／载体恒等／单例计算。               *)

Section UaftCarrier.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.

(* uaft_swap_of_sum_eq_list_explicit：源模块 p7d_swap_of_sum_eq_list 的全称形  *)
(*   ——求和实例 SO、enum 与 sum_eq_list 证书由节内 Variable 升为 forall      *)
(*   显式前提，对任意 f 成立。 *)
Theorem uaft_swap_of_sum_eq_list_explicit :
  forall (SO : SumOver RI SS) (enum : list S)
         (sum_eq_list : forall g : S -> R,
            Id (@sum_over_S RI SS SO g) (AttnDoeblin.bs_list_sum g enum))
         (f : S -> S -> R),
  Id (@sum_over_S RI SS SO (fun s : S => @sum_over_S RI SS SO (fun s' : S => f s s')))
     (@sum_over_S RI SS SO (fun s' : S => @sum_over_S RI SS SO (fun s : S => f s s'))).
Proof.
  intros SO enum sum_eq_list f.
  exact (p7d_swap_of_sum_eq_list enum sum_eq_list f).
Qed.

(* uaft_swap_list_carrier_id：以 bs_list_sum 折叠为求和载体——交换恒等即     *)
(*   双重列表和的 Fubini 恒等式（经 p7d_lsum_fubini_gen），无需 SumOver 实例。 *)
Theorem uaft_swap_list_carrier_id :
  forall (enum : list S) (f : S -> S -> R),
  Id (AttnDoeblin.bs_list_sum
        (fun s : S => AttnDoeblin.bs_list_sum (fun s' : S => f s s') enum) enum)
     (AttnDoeblin.bs_list_sum
        (fun s' : S => AttnDoeblin.bs_list_sum (fun s : S => f s s') enum) enum).
Proof.
  intros enum f.
  exact (p7d_lsum_fubini_gen f enum enum).
Qed.

(* uaft_swap_singleton_carrier：enum:=(szero::nil)——内外两折叠在单例载体上   *)
(*   定义性归约为同一形（id_refl，不经引理）。 *)
Theorem uaft_swap_singleton_carrier :
  forall f : S -> S -> R,
  Id (AttnDoeblin.bs_list_sum
        (fun s : S => AttnDoeblin.bs_list_sum (fun s' : S => f s s') (szero :: nil))
        (szero :: nil))
     (AttnDoeblin.bs_list_sum
        (fun s' : S => AttnDoeblin.bs_list_sum (fun s : S => f s s') (szero :: nil))
        (szero :: nil)).
Proof.
  intro f.
  exact id_refl.
Qed.

End UaftCarrier.

(* ---- 收尾段：逐件 Print Assumptions 核验零承认 ---- *)
Print Assumptions uaft_one_le_hi_sq_one.
Print Assumptions uaft_one_le_hi_sq_indep.
Print Assumptions uaft_factor_over_hi_one.
Print Assumptions uaft_singleton_nR_pos.
Print Assumptions uaft_singleton_nonempty_hand.
Print Assumptions uaft_singleton_nonempty_via_mother.
Print Assumptions uaft_swap_of_sum_eq_list_explicit.
Print Assumptions uaft_swap_list_carrier_id.
Print Assumptions uaft_swap_singleton_carrier.
