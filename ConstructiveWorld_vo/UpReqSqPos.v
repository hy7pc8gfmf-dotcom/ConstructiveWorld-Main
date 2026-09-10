(* UpReqSqPos.v — 槽放电战役波1 #5：square_nonneg 一器双吃（Real 层具体实例化放电）
   槽位（两处挂 T2① square_nonneg 槽的消费定理，实读定形）：
   ① UpReqAlign.v L1122（ReqNaturalGradient 节 Hypothesis 位）：
        req_square_nonneg : forall a : R, le zero (mult a a)
      直接消费 = req_fisher_zero_implies_pointwise @L1140（逐点非负桥 + 零和分解）。
   ② UpReqDist.v L969（req_group_variance_le_raw_second_moment 定理首参显式位）：
        (forall a : R, le zero (mult a a)) ->
        le req_group_variance (mult (inv_pos …) req_group_raw_second_moment)
   ----------------------------------------------------------------
   数学路线判读（侦察定案）：
   1. 槽形的 le 在 Real 实例（RealEnhancedReal）下展开 = real_le x y :=
      Or (real_lt x y) (real_eq x y)——析取强序（CW219 L3521）。
      plain 形 `le zero (t·t)` 在柯西层构造性不可证：它要求对任意 t 给出
      「t·t 严格正（带正下界见证）或 t·t == 0」的析取判定，等价于
      零分离判定；对收敛速率未知的柯西序列不可构造（普查 L375 GX 判词
      「实数序判定性不可证；只能保留显式参或改 eps 近似形」同款）。
      先例：CW219 接口全部非严格非负字段 abs_nonneg / pos_part_nonneg /
      metric_pos / log_le_linear_eps 均取逐 eps Bishop 形（E152-5：
      real_le 析取形无法表达「不趋近」等号点）；real_square_nonneg_eps
      @L44842 也只交付逐 eps 形。
   2. 普查 G2 引擎 UpRealLeB.real_square_nonneg_B@424 形状 =
      real_le_b real_zero (t·t)（forall eps>0, real_lt zero (t²+eps) 弱序）；
      单向桥 real_le_to_le_b @UpRealLeB:78 方向为 real_le ⟹ real_le_b，
      反向不可导——故 plain 槽不可由在盘引擎直放（精确阻塞裁决见尾注）。
   3. 本席交付（消费件本体不動，放电实例件与之并存）：
      [放电器·保底] sqp_square_nonneg_eps —— 接口逐 eps Bishop 形
        （le/mult/plus/zero/lt 全接口投影，直连 CW219 real_square_nonneg_eps，
        δ 透明同形映射，T2 模板②手法 = UpReqU2 log_req_compat_real 同款）。
      [辅件] sqp_opp_le_of_plus_nonneg —— le zero (a+eps) ⟹ opp a ≤ eps
        （Real 层；req_opp_plus 为 Real 层在盘件，抽象接口无 opp 对 plus
        分配字段，抽象层同形件不可导——次级发现，见尾注）。
      [主件·真放电] sqp_group_variance_le_raw_second_moment_eps_real ——
        消费②的 Real 实例逐 eps 升级形：逐 eps 平方非负喂入，得
        var ≤ (1/G)·Σr² + eps（∀eps>0，Bishop 形），不经阻塞槽。
      [保底·槽位隔离实例化] sqp_fisher_zero_implies_pointwise_real /
        sqp_group_variance_le_raw_second_moment_real —— 两消费定理的
        @ 全显节参数 Real 实例化形态，唯一余留前提即槽本身
        （forall a : Real, le zero (mult a a)）；柯西层 plain 件一旦在盘
        （口径决策后），放电 = 单参喂入一行。
   ----------------------------------------------------------------
   边界与判词（诚实账）：
   - plain 槽在 Real 层不可放电（构造性判定性阻塞，非缺件可拼）；
   - 抽象接口层亦不可导：接口缺序二分字段（Or (le zero t) (lt t zero)，
     序三分律片段，基座已明移除）且缺 opp 分配字段（req_opp_plus 仅
     Real 层在盘）——两条抽象导出路线均断；
   - 零新假设、零经典规则；全部语句 Set 层（le/req/lt 均 Set 值）。 *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqAlign.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 件1（放电器·保底）：Real 层平方非负，接口逐 eps Bishop 形        *)
(*   与接口自身非负字段（abs_nonneg 等）同款形态；直连             *)
(*   CW219 real_square_nonneg_eps（real_le/real_mult 具体层同形）。*)
(* ============================================================ *)
Lemma sqp_square_nonneg_eps : forall (t eps : Real),
  lt zero eps -> le zero (plus (mult t t) eps).
Proof.
  intros t eps Heps.
  exact (real_square_nonneg_eps t eps Heps).
Qed.

(* ============================================================ *)
(* 件1a（辅件）：le zero (a+eps) ⟹ opp a ≤ eps（Real 层）。        *)
(*   主件所需的序代数桥：−μ² ≤ eps ⟺ 0 ≤ μ²+eps。                  *)
(* ============================================================ *)
Lemma sqp_opp_le_of_plus_nonneg : forall (a eps : Real),
  le zero (plus a eps) -> le (opp a) eps.
Proof.
  intros a eps H1.
  apply (le_id_r (opp a) (plus zero eps) eps).
  - (* req (plus zero eps) eps：comm + plus_zero *)
    apply (req_trans (plus zero eps) (plus eps zero) eps).
    + apply plus_comm.
    + apply plus_zero.
  - (* le (opp a) (plus zero eps) *)
    apply (le_id_l (opp a)
                   (plus (plus (opp a) (opp eps)) eps)
                   (plus zero eps)).
    + (* req (opp a) (plus (plus (opp a) (opp eps)) eps) *)
      apply (req_trans (opp a) (plus (opp a) (plus (opp eps) eps))
                       (plus (plus (opp a) (opp eps)) eps)).
      * (* req (opp a) (plus (opp a) (plus (opp eps) eps))：
           opp a == opp a + 0 == opp a + (opp eps + eps) *)
        apply (req_trans (opp a) (plus (opp a) zero)
                         (plus (opp a) (plus (opp eps) eps))).
        -- exact (req_sym (plus (opp a) zero) (opp a) (plus_zero (opp a))).
        -- apply (req_plus_compat (opp a) (opp a) zero (plus (opp eps) eps)).
           ++ apply req_refl.
           ++ (* req zero (plus (opp eps) eps) *)
              apply (req_trans zero (plus eps (opp eps)) (plus (opp eps) eps)).
              ** exact (req_sym (plus eps (opp eps)) zero (plus_opp eps)).
              ** apply plus_comm.
      * (* assoc 重排：plus (opp a) (plus (opp eps) eps)
           == plus (plus (opp a) (opp eps)) eps *)
        exact (plus_assoc (opp a) (opp eps) eps).
    + (* le (plus (plus (opp a) (opp eps)) eps) (plus zero eps)：
         −(a+eps) ≤ −0 加 eps 保序，两端 req 换装 *)
      apply (le_plus_compat (plus (opp a) (opp eps)) zero eps eps).
      * (* le (plus (opp a) (opp eps)) zero *)
        apply (le_id_l (plus (opp a) (opp eps)) (opp (plus a eps)) zero).
        -- exact (req_sym (opp (plus a eps)) (plus (opp a) (opp eps))
                    (req_opp_plus a eps)).
        -- apply (le_id_r (opp (plus a eps)) (opp zero) zero).
           ++ exact reqd_opp_zero.
           ++ apply (opp_le_compat zero (plus a eps)). exact H1.
      * apply le_refl.
Qed.

(* ============================================================ *)
(* 件2（主件·真放电）：group_variance ≤ (1/G)·Σr² 的 Real 实例      *)
(*   逐 eps 升级形（不经阻塞槽）。                                  *)
(*   数学：var == X − μ²（req_group_variance_identity）+ 0 ≤ μ²+eps  *)
(*   （件1 喂 μ）⟹ X − μ² ≤ X + eps ⟹ var ≤ X + eps。               *)
(* ============================================================ *)
Lemma sqp_group_variance_le_raw_second_moment_eps_real :
  forall (Group : Set) (group_enum : list Group)
         (group_size_pos : lt zero (reqd_of_nat (group_size Group group_enum)))
         (reward_group : Group -> Real) (eps : Real),
    lt zero eps ->
    le (req_group_variance Group group_enum group_size_pos reward_group)
       (plus (mult (inv_pos (reqd_of_nat (group_size Group group_enum))
                             group_size_pos)
                   (req_group_raw_second_moment Group group_enum reward_group))
             eps).
Proof.
  intros Group group_enum group_size_pos reward_group eps Heps.
  apply (le_id_l (req_group_variance Group group_enum group_size_pos reward_group)
                 (req_minus (mult (inv_pos (reqd_of_nat (group_size Group group_enum))
                                        group_size_pos)
                                  (req_group_raw_second_moment Group group_enum reward_group))
                            (mult (req_group_mean Group group_enum group_size_pos reward_group)
                                  (req_group_mean Group group_enum group_size_pos reward_group)))
                 (plus (mult (inv_pos (reqd_of_nat (group_size Group group_enum))
                                        group_size_pos)
                             (req_group_raw_second_moment Group group_enum reward_group))
                       eps)).
  - exact (req_group_variance_identity
             Group group_enum group_size_pos reward_group).
  - (* X − μ² ≤ X + eps ⟸ μ ≤ 换装链 *)
    unfold req_minus.
    apply (le_plus_compat (mult (inv_pos (reqd_of_nat (group_size Group group_enum))
                                      group_size_pos)
                                (req_group_raw_second_moment Group group_enum reward_group))
                          (mult (inv_pos (reqd_of_nat (group_size Group group_enum))
                                         group_size_pos)
                                (req_group_raw_second_moment Group group_enum reward_group))
                          (opp (mult (req_group_mean Group group_enum group_size_pos reward_group)
                                     (req_group_mean Group group_enum group_size_pos reward_group)))
                          eps).
    + apply le_refl.
    + (* opp μ² ≤ eps ⟸ 0 ≤ μ² + eps（件1 直接喂 μ） *)
      apply (sqp_opp_le_of_plus_nonneg
               (mult (req_group_mean Group group_enum group_size_pos reward_group)
                     (req_group_mean Group group_enum group_size_pos reward_group))
               eps).
      exact (sqp_square_nonneg_eps
               (req_group_mean Group group_enum group_size_pos reward_group)
               eps Heps).
Qed.

(* ============================================================ *)
(* 件3（保底·槽位隔离实例化）：fisher 消费件 req_fisher_zero_implies_ *)
(*   pointwise（UpReqAlign L1140）的 @ 全显节参数 Real 实例化形态。   *)
(*   唯一余留前提 = 槽本身（forall a : Real, le zero (mult a a)）；   *)
(*   柯西层 plain 件在盘后放电 = 该参数单喂一行。                    *)
(* ============================================================ *)
Lemma sqp_fisher_zero_implies_pointwise_real :
  forall (S Theta : Set) (sumf : (S -> Real) -> Real),
    (forall f : S -> Real,
       (forall s : S, le zero (f s)) ->
       req (sumf f) zero -> forall s : S, req (f s) zero) ->
    (forall a : Real, le zero (mult a a)) ->
    forall (p_theta : Theta -> S -> Real)
           (partial : (Theta -> Real) -> Theta -> Real)
           (p_theta_pos : forall (theta : Theta) (s : S), lt zero (p_theta theta s)),
      forall theta : Theta,
        req (fisher_info_scalar_req S sumf Theta p_theta partial p_theta_pos theta)
            zero ->
        forall s : S,
          req (mult (p_theta theta s)
                    (mult (partial (fun th : Theta => log (p_theta th s) (p_theta_pos th s)) theta)
                          (partial (fun th : Theta => log (p_theta th s) (p_theta_pos th s)) theta)))
              zero.
Proof.
  intros S Theta sumf Hsumz Hsq p_theta partial p_theta_pos.
  exact (@req_fisher_zero_implies_pointwise Real RealEnhancedReal S sumf Hsumz Hsq
           Theta p_theta partial p_theta_pos).
Qed.

(* ============================================================ *)
(* 件4（保底·槽位隔离实例化）：group_variance 消费件                  *)
(*   req_group_variance_le_raw_second_moment（UpReqDist L965）的      *)
(*   @ 全显节参数 Real 实例化形态；余留前提同 = 槽本身。              *)
(* ============================================================ *)
Lemma sqp_group_variance_le_raw_second_moment_real :
  forall (Group : Set) (group_enum : list Group)
         (group_size_pos : lt zero (reqd_of_nat (group_size Group group_enum)))
         (reward_group : Group -> Real),
    (forall a : Real, le zero (mult a a)) ->
    le (req_group_variance Group group_enum group_size_pos reward_group)
       (mult (inv_pos (reqd_of_nat (group_size Group group_enum)) group_size_pos)
             (req_group_raw_second_moment Group group_enum reward_group)).
Proof.
  intros Group group_enum group_size_pos reward_group Hsq.
  exact (@req_group_variance_le_raw_second_moment Real RealEnhancedReal
           Group group_enum group_size_pos reward_group Hsq).
Qed.

(* ============================================================ *)
(* 尾注：精确阻塞裁决（兜底账）                                       *)
(* ---------------------------------------------------------------- *)
(* 阻塞点（唯一）：槽形 forall a, le zero (mult a a) 的柯西层 plain 件。 *)
(* 1. 接口侧：RealInterfaceEnhancedSetoid 的非严格 le 为析取强序        *)
(*    （Real 实例：Or real_lt real_eq），导出 plain 平方非负需序二分    *)
(*    字段 Or (le zero t) (lt t zero)——序三分律片段，基座明移除         *)
(*    （L193 注），不可增；且接口无 opp 分配字段（req_opp_plus 仅       *)
(*    Real 层在盘，UpReqAlgebra L167），抽象层连件1a 同形桥都不可导。    *)
(* 2. 柯西侧：real_le 的 Or 形使 plain 件等价零分离判定（收敛速率未知   *)
(*    的柯西序列上不可构造）；在盘最近件 = real_square_nonneg_eps       *)
(*    （CW219 L44842，逐 eps）/ real_square_nonneg_B（UpRealLeB L424，  *)
(*    le_b 弱形）；real_le_to_le_b 桥单向（le⟹le_b），反向缺口。        *)
(* 3. 解堵路线（归主会话口径决策，本席不硬凑）：                        *)
(*    a. 槽语句逐 eps 化：square_nonneg ⟦forall eps, lt zero eps ->     *)
(*       le zero (plus (mult a a) eps)⟧——件1 即放电器，两消费件随      *)
(*       逐 eps 改述全放（消费②的改述形态 = 件2 已示范）；              *)
(*    b. 槽语句 le_b 化（普查 L375 UpReqLatticeB 路线）——               *)
(*       UpRealLeB.real_square_nonneg_B 直喂；                          *)
(*    c. 维持诚实 Variable 位（与 Id 系 L24301 同判词）。               *)
(* 本文件对两消费定理本体零改动（消费件本体不動）；件2 与件3/件4 并存。  *)
(* ============================================================ *)
