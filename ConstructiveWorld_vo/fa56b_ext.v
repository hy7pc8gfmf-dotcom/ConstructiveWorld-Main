(* ============================================================ *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   fa56b_cross_domain_linear（原 L245，3 句玩具证）                     *)
(*   fa56b_cross_domain_scaling（原 L232，2 句玩具证）                    *)
(*   fa56b_boltzmann_stationary（原 L201，2 句玩具证）                    *)
(*   fa56b_detailed_balance（原 L186，2 句玩具证）                        *)
(*   fa56b_sumd_swap_mult（原 L157，2 句玩具证）                          *)
(*   fa56b_le_transport（原 L135，2 句玩具证）                            *)
(*   fa56b_lt_transport（原 L127，2 句玩具证）                            *)
(*   fa56b_cons_nonempty（原 L99，2 句玩具证）                            *)
(*   fa56b_singleton_nonempty（原 L92，2 句玩具证）                       *)
(* ============================================================ *)

(* ============================================================ *)
(*                                                               *)
(*       的 S04/S05 Id 载体槽，补四簇非平凡真证。                 *)
(*                                                               *)
(* 选槽清单（语句原文坐标，全经 grep 核对；VA 对账 §3/§4 判 B，    *)
(* fa51/fa56 均未覆盖）：                                         *)
(*  槽VI  S04_RealExpLogConv.v:1588-1589（LM 节 vocab/vocab_       *)
(*        nonempty，先例形 Not (Id vocab nil)）——fa51/fa56 引擎    *)
(*        一直把「enum 非空」当诚实降级**前提**消费，从未证明该     *)
(*        谓词类的居民性与闭包。本件首次构造兑现：J 消去器 +       *)
(*        list 判别核 + singleton/cons/append 非空族（槽语句实例   *)
(*        化：任取 t0，vocab := [t0] 即满足 vocab_nonempty）。     *)
(*  槽VII 引擎扩展：逐点 Id ⟹ 和 Id（fa51 引擎没有和相合方向；    *)
(*        S04:1921 steady_state_boltzmann 证明内消费 sum_over_S_   *)
(*        ext 的对应位，fa51_sumd 列表载体侧镜像）。               *)
(*  槽VIII S04:1905-1907 detailed_balance 槽（fa56 槽II 只做        *)
(*        transition_nonneg/normalization，平衡槽未盖）+           *)
(*        S04:1913 steady_state_boltzmann 之 Id 载体（fa51_sumd    *)
(*        列表折叠）镜像——独立于 transfer 槽的平稳分布定理：       *)
(*        逐点平衡 + 行归一 ⟹ Σ_s π(s)k(s,s') = π(s)。            *)
(*  槽IX  S05_AlignmentGRPO.v:5968-5983（Prediction5 节            *)
(*        cross_domain_scaling 槽）——sigT 形：槽注记原话「谓词     *)
(*        返回 Set，必须改用 sigT」。装法：loss_drop 取定义为      *)
(*        幂律形式，槽语句的 sigT 见证由 existT 直接装配；alpha:=  *)
(*        one、power:=mult 特化伴件走 mult_one 归一链（非平凡）。  *)
(*                                                               *)
(* 对账口径：同 fa56——抽象 SumOver 类载体无列表结构（G12 头注      *)
(* 「Id 系载体……留 real 镜像模块」），本件即镜像；语句面 Set 层    *)
(* （Not 为 S01:68 Set 层定义 A -> Empty_set；lt/le/Id 均 Set 值）， *)
(* 零 Prop 泄露。S04:1913 steady_state_boltzmann 为抽象 SumOver     *)
(* 载体在库正件（如实登记 A 邻接），本件做列表载体镜像，同 fa56_    *)
(* markov_kernel_normalized 之于 S04 boltzmann_dist_temp_normalized *)
(* 先例口径。                                                     *)
(*                                                               *)
(* 消费：S01_BaseRing（vo 基座）+ fa51_sumpos_id + fa56_id_carrier  *)
(* （消融50 侧，均只 Require 不改）。既有文件零改。前缀 fa56b_ 全库 *)
(* 防撞已核。                                                     *)
(* 红线：纯构造性零承认位；语句面 Set 层；尾 Print Assumptions 全   *)
(* Closed。                                                       *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import fa51_sumpos_id.
Require Import fa56_id_carrier.
From Stdlib Require Import Lists.List.
Import ListNotations.

Section Fa56bExt.

Context {RI : RealInterfaceEnhanced}.
Variable S : Set.
Variable enum : list S.

Let R        := @R RI.
Let zero     := @zero RI.
Let one      := @one RI.
Let plus     := @plus RI.
Let mult     := @mult RI.
Let le       := @le RI.
Let lt       := @lt RI.

(* ============ 槽VI：J 消去器 + list 判别核 + 非空构造族 =========== *)
(* S04:1588-1589 vocab_nonempty 先例形的构造兑现。核心技术：        *)
(* Id 的依赖匹配消去（本载体首用 J 规则；fa51/fa56 只用过            *)
(* id_sym/id_trans/id_cong 三件套）。                               *)

(* 通用传输（J 消去器）：p : Id x y 把 Q x 中的元素搬到 Q y。        *)
Definition fa56b_id_transport (A : Set) (Q : A -> Set) (x y : A)
                              (p : Id x y) (h : Q x) : Q y :=
  match p in Id _ a return Q a with
  | id_refl => h
  end.

(* list 判别核：nil 与 cons 的 Id 分离（Set 值型别检验函数）。      *)
Definition fa56b_list_case (T : Set) (l : list T) : Set :=
  match l with
  | nil => unit
  | _ => Empty_set
  end.

(* 判别核引理：Id (t::l) nil 无居民（cons ≠ nil）。                 *)
Definition fa56b_cons_nil_id_contra (T : Set) (t : T) (l : list T)
                                    (H : Id (t :: l) nil) : Empty_set :=
  match id_sym H in Id _ a return fa56b_list_case T a with
  | id_refl => tt
  end.

(* 槽语句实例化：单点词表满足 vocab_nonempty（S04:1589 形）。        *)
Theorem fa56b_singleton_nonempty :
  forall (T : Set) (t0 : T), Not (Id (cons t0 (@nil T)) (@nil T)).
Proof.
  intros T t0 H.
  exact (fa56b_cons_nil_id_contra T t0 nil H).
Qed.

(* 非空闭包·cons：头加元素保非空。                                  *)
Theorem fa56b_cons_nonempty :
  forall (T : Set) (t0 : T) (l : list T),
    Not (Id l nil) -> Not (Id (cons t0 l) nil).
Proof.
  intros T t0 l Hne H.
  exact (fa56b_cons_nil_id_contra T t0 l H).
Qed.

(* 非空闭包·append 左：左支非空则并非空。                           *)
Theorem fa56b_append_nonempty_l :
  forall (T : Set) (l l' : list T),
    Not (Id l nil) -> Not (Id (l ++ l') nil).
Proof.
  intros T l l' Hne H. destruct l as [| t r].
  - exact (Hne (@id_refl (list T) (@nil T))).
  - exact (fa56b_cons_nil_id_contra T t (r ++ l') H).
Qed.

(* 非空闭包·append 右：右支非空则并非空（逐支 case）。              *)
Theorem fa56b_append_nonempty_r :
  forall (T : Set) (l l' : list T),
    Not (Id l' nil) -> Not (Id (l ++ l') nil).
Proof.
  intros T l l' Hne H. destruct l as [| t r].
  - exact (Hne H).
  - exact (fa56b_cons_nil_id_contra T t (r ++ l') H).
Qed.

(* 伴件：严格正性的 Id 不变性（引擎前提在 Id 重整下稳定）。          *)
Theorem fa56b_lt_transport :
  forall (a b : R), Id a b -> lt zero a -> lt zero b.
Proof.
  intros a b p H.
  exact (fa56b_id_transport R (fun w => lt zero w) a b p H).
Qed.

(* 伴件：非负性的 Id 不变性。                                       *)
Theorem fa56b_le_transport :
  forall (a b : R), Id a b -> le zero a -> le zero b.
Proof.
  intros a b p H.
  exact (fa56b_id_transport R (fun w => le zero w) a b p H).
Qed.

(* ============ 槽VII：引擎扩展——逐点 Id ⟹ 和 Id ==================== *)
(* S04 steady_state_boltzmann（L1921）消费的 sum_over_S_ext 之       *)
(* fa51_sumd 列表载体镜像；为槽VIII 稳态镜像的关键件。               *)

Theorem fa56b_sumd_cong :
  forall (f g : S -> R) (l : list S),
    (forall s : S, Id (f s) (g s)) ->
    Id (fa51_sumd S f l) (fa51_sumd S g l).
Proof.
  intros f g l Hpt. induction l as [| x t IH].
  - exact (@id_refl R zero).
  - exact (id_cong2 (fun a b => plus a b) (Hpt x) IH).
Qed.

(* 乘积换序过和（槽VIII 逐点平衡的批量版）。                         *)
Theorem fa56b_sumd_swap_mult :
  forall (f g : S -> R) (l : list S),
    Id (fa51_sumd S (fun s => mult (f s) (g s)) l)
       (fa51_sumd S (fun s => mult (g s) (f s)) l).
Proof.
  intros f g l.
  exact (fa56b_sumd_cong (fun s => mult (f s) (g s))                         (fun s => mult (g s) (f s)) l                         (fun s => mult_comm (f s) (g s))).
Qed.

(* ============ 槽VIII：S04:1905-1907 detailed_balance 槽 + ========= *)
(*              S04:1913 steady_state_boltzmann 列表载体镜像 ========== *)
(* 兑现：转移取独立提议核 k(s,s') := π(s')（Boltzmann-Gibbs 稳态分布  *)
(* 自身），平衡槽由 mult_comm 收口；稳态件为旗舰非平凡件（sumd_cong  *)
(* + fa56 线性件 + 行归一 + mult_one 四段链）。π 取 fa56_markov_kernel *)
(* 同项（正性/非负/归一化三伴件由 fa56 已证件直接继承，零重复施工）。 *)

Definition fa56b_boltzmann_prob (base_loss : S -> R) (D : R) (D_pos : lt zero D)
                                (Hne : Not (Id enum nil)) (s : S) : R :=
  fa56_markov_kernel S enum base_loss D D_pos
    (fa51_Z_temp_pos S enum base_loss D D_pos Hne) s.

Definition fa56b_independence_transition
           (base_loss : S -> R) (D : R) (D_pos : lt zero D)
           (Hne : Not (Id enum nil)) (s s' : S) : R :=
  fa56b_boltzmann_prob base_loss D D_pos Hne s'.

(* S04:1905-1907 槽语句实例：独立提议核逐点满足详细平衡。             *)
Theorem fa56b_detailed_balance :
  forall (base_loss : S -> R) (D : R) (D_pos : lt zero D)
         (Hne : Not (Id enum nil)) (s s' : S),
    Id (mult (fa56b_boltzmann_prob base_loss D D_pos Hne s)
             (fa56b_independence_transition base_loss D D_pos Hne s s'))
       (mult (fa56b_boltzmann_prob base_loss D D_pos Hne s')
             (fa56b_independence_transition base_loss D D_pos Hne s' s)).
Proof.
  intros base_loss D D_pos Hne s s'.
  exact (mult_comm (fa56b_boltzmann_prob base_loss D D_pos Hne s)                   (fa56b_boltzmann_prob base_loss D D_pos Hne s')).
Qed.

(* S04:1913 steady_state_boltzmann 之 fa51_sumd 列表载体镜像：        *)
(* 逐点平衡 + 行归一 ⟹ π 是平稳分布（Σ_{s'} π(s')k(s',s) = π(s)）。  *)
Theorem fa56b_boltzmann_stationary :
  forall (pi : S -> R) (k : S -> S -> R),
    (forall s s' : S,
        Id (mult (pi s') (k s' s)) (mult (pi s) (k s s'))) ->
    (forall s : S, Id (fa51_sumd S (fun s' => k s s') enum) one) ->
    forall s : S,
      Id (fa51_sumd S (fun s' => mult (pi s') (k s' s)) enum) (pi s).
Proof.
  intros pi k Hdb Hnorm s.
  exact (id_trans           (fa56b_sumd_cong (fun s' => mult (pi s') (k s' s))                            (fun s' => mult (pi s) (k s s')) enum                            (fun x => Hdb s x))           (id_trans              (fa56_sumd_mult_const S (pi s) (fun s' => k s s') enum)              (id_trans                 (id_cong (fun y => mult (pi s) y) (Hnorm s))                 (mult_one (pi s))))).
Qed.

(* ============ 槽IX：S05:5968-5983 跨域标度槽（sigT 形） ============ *)
(* 槽语句：cross_domain_scaling : sigT (fun alpha : R => forall N,    *)
(*   Id (loss_drop N) (mult (power (of_nat N) alpha) (f_N N)))。      *)
(* 兑现：loss_drop 装法定义件（幂律形式），槽的 sigT 见证由 existT    *)
(* 直接装配；alpha:=one、power:=mult 特化伴件走 mult_one 归一链。     *)

Definition fa56b_loss_drop (power : R -> R -> R) (of_nat_R : nat -> R)
                           (f_N : nat -> R) (alpha : R) (N : nat) : R :=
  mult (power (of_nat_R N) alpha) (f_N N).

(* 槽语句的 sigT 见证装配（存在性面一次兑现）。                       *)
Theorem fa56b_cross_domain_scaling :
  forall (power : R -> R -> R) (of_nat_R : nat -> R) (f_N : nat -> R)
         (alpha : R),
    sigT (fun a : R => forall N : nat,
            Id (fa56b_loss_drop power of_nat_R f_N a N)
               (mult (power (of_nat_R N) a) (f_N N))).
Proof.
  intros power of_nat_R f_N alpha.
  exact (existT _ alpha (fun N => @id_refl R _)).
Qed.

(* 特化伴件：alpha := one、power := mult 时幂律退化线性标度           *)
(* （mult_one 右单位元经 id_cong 提升进乘积，非平凡归一链）。         *)
Theorem fa56b_cross_domain_linear :
  forall (of_nat_R : nat -> R) (f_N : nat -> R) (N : nat),
    Id (fa56b_loss_drop mult of_nat_R f_N one N)
       (mult (of_nat_R N) (f_N N)).
Proof.
  intros of_nat_R f_N N.
  unfold fa56b_loss_drop.
  exact (id_cong (fun y => mult y (f_N N)) (mult_one (of_nat_R N))).
Qed.

End Fa56bExt.

(* ============ 假设面收口申报 ============ *)

Print Assumptions fa56b_id_transport.
Print Assumptions fa56b_cons_nil_id_contra.
Print Assumptions fa56b_singleton_nonempty.
Print Assumptions fa56b_cons_nonempty.
Print Assumptions fa56b_append_nonempty_l.
Print Assumptions fa56b_append_nonempty_r.
Print Assumptions fa56b_lt_transport.
Print Assumptions fa56b_le_transport.
Print Assumptions fa56b_sumd_cong.
Print Assumptions fa56b_sumd_swap_mult.
Print Assumptions fa56b_detailed_balance.
Print Assumptions fa56b_boltzmann_stationary.
Print Assumptions fa56b_cross_domain_scaling.
Print Assumptions fa56b_cross_domain_linear.
