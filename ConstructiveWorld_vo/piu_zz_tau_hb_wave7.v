(* piu_zz_tau_hb_wave7.v — KB11 Hb 升格候选子片 7/8（1024 段 Hb64-Hb79·机械升格件·零漂移回读断言已过）。
   使命：consumer 片 assert (HbN : <封闭语句>) + brace 块逐块升格为独立引理（语句/证明体逐字保留，
         抽取器对每生成件回读 diff 断言通过），使 128 小件可全并行独立编译（各自独立进程内存清零），
         替代 20h 单体磨；本件为候选稿，落地须过试炮与终门，不替代正本。
   依赖：piu_zz_tau_enclosure_bank4（Require Export 链末前件，传递覆盖 bank1..bank3 与 base）、
         piu_zz_poincare_engine、piu_zz_padic_clearing、Stdlib QArith/ZArith/Arith/PArith/Lia/List。
   对标：piu_zz_tau_enclosure.v（3275 行 post-fix·原巨件 md5 494c8738 分段账）zzPhi_512 段 L103-L774 /
         zzPhi_1024 段 L1019-L3034 的 assert (HbN) 块逐字升格。
   构造性：本片语句零假设、零公理；语句全封闭（右边=bank 事实闭式积），
         证明体只吃 bank 引理＋cbn＋reflexivity；块间零依赖边（ledger 实测）。
   编译配方: coqc -time -native-compiler no -q -Q . "" piu_zz_tau_hb_wave7.v *)
Require Export piu_zz_tau_enclosure_bank4.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.

(* src piu_zz_tau_enclosure.v L2363-L2383 (assert Hb64) *)
Lemma piu_zz_hb_1024_64 : piu_zz_zprod_seg 1024%nat (512%nat + 496%nat) 16%nat = ((if zz_in_Pn 1024 1009%nat then Z.of_nat 1009%nat else 1%Z) * ((if zz_in_Pn 1024 1010%nat then Z.of_nat 1010%nat else 1%Z) * ((if zz_in_Pn 1024 1011%nat then Z.of_nat 1011%nat else 1%Z) * ((if zz_in_Pn 1024 1012%nat then Z.of_nat 1012%nat else 1%Z) * ((if zz_in_Pn 1024 1013%nat then Z.of_nat 1013%nat else 1%Z) * ((if zz_in_Pn 1024 1014%nat then Z.of_nat 1014%nat else 1%Z) * ((if zz_in_Pn 1024 1015%nat then Z.of_nat 1015%nat else 1%Z) * ((if zz_in_Pn 1024 1016%nat then Z.of_nat 1016%nat else 1%Z) * ((if zz_in_Pn 1024 1017%nat then Z.of_nat 1017%nat else 1%Z) * ((if zz_in_Pn 1024 1018%nat then Z.of_nat 1018%nat else 1%Z) * ((if zz_in_Pn 1024 1019%nat then Z.of_nat 1019%nat else 1%Z) * ((if zz_in_Pn 1024 1020%nat then Z.of_nat 1020%nat else 1%Z) * ((if zz_in_Pn 1024 1021%nat then Z.of_nat 1021%nat else 1%Z) * ((if zz_in_Pn 1024 1022%nat then Z.of_nat 1022%nat else 1%Z) * ((if zz_in_Pn 1024 1023%nat then Z.of_nat 1023%nat else 1%Z) * (if zz_in_Pn 1024 1024%nat then Z.of_nat 1024%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1024.
    rewrite piu_zz_inPn_1024_1023.
    rewrite piu_zz_inPn_1024_1022.
    rewrite piu_zz_inPn_1024_1021.
    rewrite piu_zz_inPn_1024_1020.
    rewrite piu_zz_inPn_1024_1019.
    rewrite piu_zz_inPn_1024_1018.
    rewrite piu_zz_inPn_1024_1017.
    rewrite piu_zz_inPn_1024_1016.
    rewrite piu_zz_inPn_1024_1015.
    rewrite piu_zz_inPn_1024_1014.
    rewrite piu_zz_inPn_1024_1013.
    rewrite piu_zz_inPn_1024_1012.
    rewrite piu_zz_inPn_1024_1011.
    rewrite piu_zz_inPn_1024_1010.
    rewrite piu_zz_inPn_1024_1009.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2384-L2404 (assert Hb65) *)
Lemma piu_zz_hb_1024_65 : piu_zz_zprod_seg 1024%nat (512%nat + 480%nat) 16%nat = ((if zz_in_Pn 1024 993%nat then Z.of_nat 993%nat else 1%Z) * ((if zz_in_Pn 1024 994%nat then Z.of_nat 994%nat else 1%Z) * ((if zz_in_Pn 1024 995%nat then Z.of_nat 995%nat else 1%Z) * ((if zz_in_Pn 1024 996%nat then Z.of_nat 996%nat else 1%Z) * ((if zz_in_Pn 1024 997%nat then Z.of_nat 997%nat else 1%Z) * ((if zz_in_Pn 1024 998%nat then Z.of_nat 998%nat else 1%Z) * ((if zz_in_Pn 1024 999%nat then Z.of_nat 999%nat else 1%Z) * ((if zz_in_Pn 1024 1000%nat then Z.of_nat 1000%nat else 1%Z) * ((if zz_in_Pn 1024 1001%nat then Z.of_nat 1001%nat else 1%Z) * ((if zz_in_Pn 1024 1002%nat then Z.of_nat 1002%nat else 1%Z) * ((if zz_in_Pn 1024 1003%nat then Z.of_nat 1003%nat else 1%Z) * ((if zz_in_Pn 1024 1004%nat then Z.of_nat 1004%nat else 1%Z) * ((if zz_in_Pn 1024 1005%nat then Z.of_nat 1005%nat else 1%Z) * ((if zz_in_Pn 1024 1006%nat then Z.of_nat 1006%nat else 1%Z) * ((if zz_in_Pn 1024 1007%nat then Z.of_nat 1007%nat else 1%Z) * (if zz_in_Pn 1024 1008%nat then Z.of_nat 1008%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1008.
    rewrite piu_zz_inPn_1024_1007.
    rewrite piu_zz_inPn_1024_1006.
    rewrite piu_zz_inPn_1024_1005.
    rewrite piu_zz_inPn_1024_1004.
    rewrite piu_zz_inPn_1024_1003.
    rewrite piu_zz_inPn_1024_1002.
    rewrite piu_zz_inPn_1024_1001.
    rewrite piu_zz_inPn_1024_1000.
    rewrite piu_zz_inPn_1024_999.
    rewrite piu_zz_inPn_1024_998.
    rewrite piu_zz_inPn_1024_997.
    rewrite piu_zz_inPn_1024_996.
    rewrite piu_zz_inPn_1024_995.
    rewrite piu_zz_inPn_1024_994.
    rewrite piu_zz_inPn_1024_993.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2405-L2425 (assert Hb66) *)
Lemma piu_zz_hb_1024_66 : piu_zz_zprod_seg 1024%nat (512%nat + 464%nat) 16%nat = ((if zz_in_Pn 1024 977%nat then Z.of_nat 977%nat else 1%Z) * ((if zz_in_Pn 1024 978%nat then Z.of_nat 978%nat else 1%Z) * ((if zz_in_Pn 1024 979%nat then Z.of_nat 979%nat else 1%Z) * ((if zz_in_Pn 1024 980%nat then Z.of_nat 980%nat else 1%Z) * ((if zz_in_Pn 1024 981%nat then Z.of_nat 981%nat else 1%Z) * ((if zz_in_Pn 1024 982%nat then Z.of_nat 982%nat else 1%Z) * ((if zz_in_Pn 1024 983%nat then Z.of_nat 983%nat else 1%Z) * ((if zz_in_Pn 1024 984%nat then Z.of_nat 984%nat else 1%Z) * ((if zz_in_Pn 1024 985%nat then Z.of_nat 985%nat else 1%Z) * ((if zz_in_Pn 1024 986%nat then Z.of_nat 986%nat else 1%Z) * ((if zz_in_Pn 1024 987%nat then Z.of_nat 987%nat else 1%Z) * ((if zz_in_Pn 1024 988%nat then Z.of_nat 988%nat else 1%Z) * ((if zz_in_Pn 1024 989%nat then Z.of_nat 989%nat else 1%Z) * ((if zz_in_Pn 1024 990%nat then Z.of_nat 990%nat else 1%Z) * ((if zz_in_Pn 1024 991%nat then Z.of_nat 991%nat else 1%Z) * (if zz_in_Pn 1024 992%nat then Z.of_nat 992%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_992.
    rewrite piu_zz_inPn_1024_991.
    rewrite piu_zz_inPn_1024_990.
    rewrite piu_zz_inPn_1024_989.
    rewrite piu_zz_inPn_1024_988.
    rewrite piu_zz_inPn_1024_987.
    rewrite piu_zz_inPn_1024_986.
    rewrite piu_zz_inPn_1024_985.
    rewrite piu_zz_inPn_1024_984.
    rewrite piu_zz_inPn_1024_983.
    rewrite piu_zz_inPn_1024_982.
    rewrite piu_zz_inPn_1024_981.
    rewrite piu_zz_inPn_1024_980.
    rewrite piu_zz_inPn_1024_979.
    rewrite piu_zz_inPn_1024_978.
    rewrite piu_zz_inPn_1024_977.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2426-L2446 (assert Hb67) *)
Lemma piu_zz_hb_1024_67 : piu_zz_zprod_seg 1024%nat (512%nat + 448%nat) 16%nat = ((if zz_in_Pn 1024 961%nat then Z.of_nat 961%nat else 1%Z) * ((if zz_in_Pn 1024 962%nat then Z.of_nat 962%nat else 1%Z) * ((if zz_in_Pn 1024 963%nat then Z.of_nat 963%nat else 1%Z) * ((if zz_in_Pn 1024 964%nat then Z.of_nat 964%nat else 1%Z) * ((if zz_in_Pn 1024 965%nat then Z.of_nat 965%nat else 1%Z) * ((if zz_in_Pn 1024 966%nat then Z.of_nat 966%nat else 1%Z) * ((if zz_in_Pn 1024 967%nat then Z.of_nat 967%nat else 1%Z) * ((if zz_in_Pn 1024 968%nat then Z.of_nat 968%nat else 1%Z) * ((if zz_in_Pn 1024 969%nat then Z.of_nat 969%nat else 1%Z) * ((if zz_in_Pn 1024 970%nat then Z.of_nat 970%nat else 1%Z) * ((if zz_in_Pn 1024 971%nat then Z.of_nat 971%nat else 1%Z) * ((if zz_in_Pn 1024 972%nat then Z.of_nat 972%nat else 1%Z) * ((if zz_in_Pn 1024 973%nat then Z.of_nat 973%nat else 1%Z) * ((if zz_in_Pn 1024 974%nat then Z.of_nat 974%nat else 1%Z) * ((if zz_in_Pn 1024 975%nat then Z.of_nat 975%nat else 1%Z) * (if zz_in_Pn 1024 976%nat then Z.of_nat 976%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_976.
    rewrite piu_zz_inPn_1024_975.
    rewrite piu_zz_inPn_1024_974.
    rewrite piu_zz_inPn_1024_973.
    rewrite piu_zz_inPn_1024_972.
    rewrite piu_zz_inPn_1024_971.
    rewrite piu_zz_inPn_1024_970.
    rewrite piu_zz_inPn_1024_969.
    rewrite piu_zz_inPn_1024_968.
    rewrite piu_zz_inPn_1024_967.
    rewrite piu_zz_inPn_1024_966.
    rewrite piu_zz_inPn_1024_965.
    rewrite piu_zz_inPn_1024_964.
    rewrite piu_zz_inPn_1024_963.
    rewrite piu_zz_inPn_1024_962.
    rewrite piu_zz_inPn_1024_961.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2447-L2467 (assert Hb68) *)
Lemma piu_zz_hb_1024_68 : piu_zz_zprod_seg 1024%nat (512%nat + 432%nat) 16%nat = ((if zz_in_Pn 1024 945%nat then Z.of_nat 945%nat else 1%Z) * ((if zz_in_Pn 1024 946%nat then Z.of_nat 946%nat else 1%Z) * ((if zz_in_Pn 1024 947%nat then Z.of_nat 947%nat else 1%Z) * ((if zz_in_Pn 1024 948%nat then Z.of_nat 948%nat else 1%Z) * ((if zz_in_Pn 1024 949%nat then Z.of_nat 949%nat else 1%Z) * ((if zz_in_Pn 1024 950%nat then Z.of_nat 950%nat else 1%Z) * ((if zz_in_Pn 1024 951%nat then Z.of_nat 951%nat else 1%Z) * ((if zz_in_Pn 1024 952%nat then Z.of_nat 952%nat else 1%Z) * ((if zz_in_Pn 1024 953%nat then Z.of_nat 953%nat else 1%Z) * ((if zz_in_Pn 1024 954%nat then Z.of_nat 954%nat else 1%Z) * ((if zz_in_Pn 1024 955%nat then Z.of_nat 955%nat else 1%Z) * ((if zz_in_Pn 1024 956%nat then Z.of_nat 956%nat else 1%Z) * ((if zz_in_Pn 1024 957%nat then Z.of_nat 957%nat else 1%Z) * ((if zz_in_Pn 1024 958%nat then Z.of_nat 958%nat else 1%Z) * ((if zz_in_Pn 1024 959%nat then Z.of_nat 959%nat else 1%Z) * (if zz_in_Pn 1024 960%nat then Z.of_nat 960%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_960.
    rewrite piu_zz_inPn_1024_959.
    rewrite piu_zz_inPn_1024_958.
    rewrite piu_zz_inPn_1024_957.
    rewrite piu_zz_inPn_1024_956.
    rewrite piu_zz_inPn_1024_955.
    rewrite piu_zz_inPn_1024_954.
    rewrite piu_zz_inPn_1024_953.
    rewrite piu_zz_inPn_1024_952.
    rewrite piu_zz_inPn_1024_951.
    rewrite piu_zz_inPn_1024_950.
    rewrite piu_zz_inPn_1024_949.
    rewrite piu_zz_inPn_1024_948.
    rewrite piu_zz_inPn_1024_947.
    rewrite piu_zz_inPn_1024_946.
    rewrite piu_zz_inPn_1024_945.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2468-L2488 (assert Hb69) *)
Lemma piu_zz_hb_1024_69 : piu_zz_zprod_seg 1024%nat (512%nat + 416%nat) 16%nat = ((if zz_in_Pn 1024 929%nat then Z.of_nat 929%nat else 1%Z) * ((if zz_in_Pn 1024 930%nat then Z.of_nat 930%nat else 1%Z) * ((if zz_in_Pn 1024 931%nat then Z.of_nat 931%nat else 1%Z) * ((if zz_in_Pn 1024 932%nat then Z.of_nat 932%nat else 1%Z) * ((if zz_in_Pn 1024 933%nat then Z.of_nat 933%nat else 1%Z) * ((if zz_in_Pn 1024 934%nat then Z.of_nat 934%nat else 1%Z) * ((if zz_in_Pn 1024 935%nat then Z.of_nat 935%nat else 1%Z) * ((if zz_in_Pn 1024 936%nat then Z.of_nat 936%nat else 1%Z) * ((if zz_in_Pn 1024 937%nat then Z.of_nat 937%nat else 1%Z) * ((if zz_in_Pn 1024 938%nat then Z.of_nat 938%nat else 1%Z) * ((if zz_in_Pn 1024 939%nat then Z.of_nat 939%nat else 1%Z) * ((if zz_in_Pn 1024 940%nat then Z.of_nat 940%nat else 1%Z) * ((if zz_in_Pn 1024 941%nat then Z.of_nat 941%nat else 1%Z) * ((if zz_in_Pn 1024 942%nat then Z.of_nat 942%nat else 1%Z) * ((if zz_in_Pn 1024 943%nat then Z.of_nat 943%nat else 1%Z) * (if zz_in_Pn 1024 944%nat then Z.of_nat 944%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_944.
    rewrite piu_zz_inPn_1024_943.
    rewrite piu_zz_inPn_1024_942.
    rewrite piu_zz_inPn_1024_941.
    rewrite piu_zz_inPn_1024_940.
    rewrite piu_zz_inPn_1024_939.
    rewrite piu_zz_inPn_1024_938.
    rewrite piu_zz_inPn_1024_937.
    rewrite piu_zz_inPn_1024_936.
    rewrite piu_zz_inPn_1024_935.
    rewrite piu_zz_inPn_1024_934.
    rewrite piu_zz_inPn_1024_933.
    rewrite piu_zz_inPn_1024_932.
    rewrite piu_zz_inPn_1024_931.
    rewrite piu_zz_inPn_1024_930.
    rewrite piu_zz_inPn_1024_929.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2489-L2509 (assert Hb70) *)
Lemma piu_zz_hb_1024_70 : piu_zz_zprod_seg 1024%nat (512%nat + 400%nat) 16%nat = ((if zz_in_Pn 1024 913%nat then Z.of_nat 913%nat else 1%Z) * ((if zz_in_Pn 1024 914%nat then Z.of_nat 914%nat else 1%Z) * ((if zz_in_Pn 1024 915%nat then Z.of_nat 915%nat else 1%Z) * ((if zz_in_Pn 1024 916%nat then Z.of_nat 916%nat else 1%Z) * ((if zz_in_Pn 1024 917%nat then Z.of_nat 917%nat else 1%Z) * ((if zz_in_Pn 1024 918%nat then Z.of_nat 918%nat else 1%Z) * ((if zz_in_Pn 1024 919%nat then Z.of_nat 919%nat else 1%Z) * ((if zz_in_Pn 1024 920%nat then Z.of_nat 920%nat else 1%Z) * ((if zz_in_Pn 1024 921%nat then Z.of_nat 921%nat else 1%Z) * ((if zz_in_Pn 1024 922%nat then Z.of_nat 922%nat else 1%Z) * ((if zz_in_Pn 1024 923%nat then Z.of_nat 923%nat else 1%Z) * ((if zz_in_Pn 1024 924%nat then Z.of_nat 924%nat else 1%Z) * ((if zz_in_Pn 1024 925%nat then Z.of_nat 925%nat else 1%Z) * ((if zz_in_Pn 1024 926%nat then Z.of_nat 926%nat else 1%Z) * ((if zz_in_Pn 1024 927%nat then Z.of_nat 927%nat else 1%Z) * (if zz_in_Pn 1024 928%nat then Z.of_nat 928%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_928.
    rewrite piu_zz_inPn_1024_927.
    rewrite piu_zz_inPn_1024_926.
    rewrite piu_zz_inPn_1024_925.
    rewrite piu_zz_inPn_1024_924.
    rewrite piu_zz_inPn_1024_923.
    rewrite piu_zz_inPn_1024_922.
    rewrite piu_zz_inPn_1024_921.
    rewrite piu_zz_inPn_1024_920.
    rewrite piu_zz_inPn_1024_919.
    rewrite piu_zz_inPn_1024_918.
    rewrite piu_zz_inPn_1024_917.
    rewrite piu_zz_inPn_1024_916.
    rewrite piu_zz_inPn_1024_915.
    rewrite piu_zz_inPn_1024_914.
    rewrite piu_zz_inPn_1024_913.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2510-L2530 (assert Hb71) *)
Lemma piu_zz_hb_1024_71 : piu_zz_zprod_seg 1024%nat (512%nat + 384%nat) 16%nat = ((if zz_in_Pn 1024 897%nat then Z.of_nat 897%nat else 1%Z) * ((if zz_in_Pn 1024 898%nat then Z.of_nat 898%nat else 1%Z) * ((if zz_in_Pn 1024 899%nat then Z.of_nat 899%nat else 1%Z) * ((if zz_in_Pn 1024 900%nat then Z.of_nat 900%nat else 1%Z) * ((if zz_in_Pn 1024 901%nat then Z.of_nat 901%nat else 1%Z) * ((if zz_in_Pn 1024 902%nat then Z.of_nat 902%nat else 1%Z) * ((if zz_in_Pn 1024 903%nat then Z.of_nat 903%nat else 1%Z) * ((if zz_in_Pn 1024 904%nat then Z.of_nat 904%nat else 1%Z) * ((if zz_in_Pn 1024 905%nat then Z.of_nat 905%nat else 1%Z) * ((if zz_in_Pn 1024 906%nat then Z.of_nat 906%nat else 1%Z) * ((if zz_in_Pn 1024 907%nat then Z.of_nat 907%nat else 1%Z) * ((if zz_in_Pn 1024 908%nat then Z.of_nat 908%nat else 1%Z) * ((if zz_in_Pn 1024 909%nat then Z.of_nat 909%nat else 1%Z) * ((if zz_in_Pn 1024 910%nat then Z.of_nat 910%nat else 1%Z) * ((if zz_in_Pn 1024 911%nat then Z.of_nat 911%nat else 1%Z) * (if zz_in_Pn 1024 912%nat then Z.of_nat 912%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_912.
    rewrite piu_zz_inPn_1024_911.
    rewrite piu_zz_inPn_1024_910.
    rewrite piu_zz_inPn_1024_909.
    rewrite piu_zz_inPn_1024_908.
    rewrite piu_zz_inPn_1024_907.
    rewrite piu_zz_inPn_1024_906.
    rewrite piu_zz_inPn_1024_905.
    rewrite piu_zz_inPn_1024_904.
    rewrite piu_zz_inPn_1024_903.
    rewrite piu_zz_inPn_1024_902.
    rewrite piu_zz_inPn_1024_901.
    rewrite piu_zz_inPn_1024_900.
    rewrite piu_zz_inPn_1024_899.
    rewrite piu_zz_inPn_1024_898.
    rewrite piu_zz_inPn_1024_897.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2531-L2551 (assert Hb72) *)
Lemma piu_zz_hb_1024_72 : piu_zz_zprod_seg 1024%nat (512%nat + 368%nat) 16%nat = ((if zz_in_Pn 1024 881%nat then Z.of_nat 881%nat else 1%Z) * ((if zz_in_Pn 1024 882%nat then Z.of_nat 882%nat else 1%Z) * ((if zz_in_Pn 1024 883%nat then Z.of_nat 883%nat else 1%Z) * ((if zz_in_Pn 1024 884%nat then Z.of_nat 884%nat else 1%Z) * ((if zz_in_Pn 1024 885%nat then Z.of_nat 885%nat else 1%Z) * ((if zz_in_Pn 1024 886%nat then Z.of_nat 886%nat else 1%Z) * ((if zz_in_Pn 1024 887%nat then Z.of_nat 887%nat else 1%Z) * ((if zz_in_Pn 1024 888%nat then Z.of_nat 888%nat else 1%Z) * ((if zz_in_Pn 1024 889%nat then Z.of_nat 889%nat else 1%Z) * ((if zz_in_Pn 1024 890%nat then Z.of_nat 890%nat else 1%Z) * ((if zz_in_Pn 1024 891%nat then Z.of_nat 891%nat else 1%Z) * ((if zz_in_Pn 1024 892%nat then Z.of_nat 892%nat else 1%Z) * ((if zz_in_Pn 1024 893%nat then Z.of_nat 893%nat else 1%Z) * ((if zz_in_Pn 1024 894%nat then Z.of_nat 894%nat else 1%Z) * ((if zz_in_Pn 1024 895%nat then Z.of_nat 895%nat else 1%Z) * (if zz_in_Pn 1024 896%nat then Z.of_nat 896%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_896.
    rewrite piu_zz_inPn_1024_895.
    rewrite piu_zz_inPn_1024_894.
    rewrite piu_zz_inPn_1024_893.
    rewrite piu_zz_inPn_1024_892.
    rewrite piu_zz_inPn_1024_891.
    rewrite piu_zz_inPn_1024_890.
    rewrite piu_zz_inPn_1024_889.
    rewrite piu_zz_inPn_1024_888.
    rewrite piu_zz_inPn_1024_887.
    rewrite piu_zz_inPn_1024_886.
    rewrite piu_zz_inPn_1024_885.
    rewrite piu_zz_inPn_1024_884.
    rewrite piu_zz_inPn_1024_883.
    rewrite piu_zz_inPn_1024_882.
    rewrite piu_zz_inPn_1024_881.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2552-L2572 (assert Hb73) *)
Lemma piu_zz_hb_1024_73 : piu_zz_zprod_seg 1024%nat (512%nat + 352%nat) 16%nat = ((if zz_in_Pn 1024 865%nat then Z.of_nat 865%nat else 1%Z) * ((if zz_in_Pn 1024 866%nat then Z.of_nat 866%nat else 1%Z) * ((if zz_in_Pn 1024 867%nat then Z.of_nat 867%nat else 1%Z) * ((if zz_in_Pn 1024 868%nat then Z.of_nat 868%nat else 1%Z) * ((if zz_in_Pn 1024 869%nat then Z.of_nat 869%nat else 1%Z) * ((if zz_in_Pn 1024 870%nat then Z.of_nat 870%nat else 1%Z) * ((if zz_in_Pn 1024 871%nat then Z.of_nat 871%nat else 1%Z) * ((if zz_in_Pn 1024 872%nat then Z.of_nat 872%nat else 1%Z) * ((if zz_in_Pn 1024 873%nat then Z.of_nat 873%nat else 1%Z) * ((if zz_in_Pn 1024 874%nat then Z.of_nat 874%nat else 1%Z) * ((if zz_in_Pn 1024 875%nat then Z.of_nat 875%nat else 1%Z) * ((if zz_in_Pn 1024 876%nat then Z.of_nat 876%nat else 1%Z) * ((if zz_in_Pn 1024 877%nat then Z.of_nat 877%nat else 1%Z) * ((if zz_in_Pn 1024 878%nat then Z.of_nat 878%nat else 1%Z) * ((if zz_in_Pn 1024 879%nat then Z.of_nat 879%nat else 1%Z) * (if zz_in_Pn 1024 880%nat then Z.of_nat 880%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_880.
    rewrite piu_zz_inPn_1024_879.
    rewrite piu_zz_inPn_1024_878.
    rewrite piu_zz_inPn_1024_877.
    rewrite piu_zz_inPn_1024_876.
    rewrite piu_zz_inPn_1024_875.
    rewrite piu_zz_inPn_1024_874.
    rewrite piu_zz_inPn_1024_873.
    rewrite piu_zz_inPn_1024_872.
    rewrite piu_zz_inPn_1024_871.
    rewrite piu_zz_inPn_1024_870.
    rewrite piu_zz_inPn_1024_869.
    rewrite piu_zz_inPn_1024_868.
    rewrite piu_zz_inPn_1024_867.
    rewrite piu_zz_inPn_1024_866.
    rewrite piu_zz_inPn_1024_865.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2573-L2593 (assert Hb74) *)
Lemma piu_zz_hb_1024_74 : piu_zz_zprod_seg 1024%nat (512%nat + 336%nat) 16%nat = ((if zz_in_Pn 1024 849%nat then Z.of_nat 849%nat else 1%Z) * ((if zz_in_Pn 1024 850%nat then Z.of_nat 850%nat else 1%Z) * ((if zz_in_Pn 1024 851%nat then Z.of_nat 851%nat else 1%Z) * ((if zz_in_Pn 1024 852%nat then Z.of_nat 852%nat else 1%Z) * ((if zz_in_Pn 1024 853%nat then Z.of_nat 853%nat else 1%Z) * ((if zz_in_Pn 1024 854%nat then Z.of_nat 854%nat else 1%Z) * ((if zz_in_Pn 1024 855%nat then Z.of_nat 855%nat else 1%Z) * ((if zz_in_Pn 1024 856%nat then Z.of_nat 856%nat else 1%Z) * ((if zz_in_Pn 1024 857%nat then Z.of_nat 857%nat else 1%Z) * ((if zz_in_Pn 1024 858%nat then Z.of_nat 858%nat else 1%Z) * ((if zz_in_Pn 1024 859%nat then Z.of_nat 859%nat else 1%Z) * ((if zz_in_Pn 1024 860%nat then Z.of_nat 860%nat else 1%Z) * ((if zz_in_Pn 1024 861%nat then Z.of_nat 861%nat else 1%Z) * ((if zz_in_Pn 1024 862%nat then Z.of_nat 862%nat else 1%Z) * ((if zz_in_Pn 1024 863%nat then Z.of_nat 863%nat else 1%Z) * (if zz_in_Pn 1024 864%nat then Z.of_nat 864%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_864.
    rewrite piu_zz_inPn_1024_863.
    rewrite piu_zz_inPn_1024_862.
    rewrite piu_zz_inPn_1024_861.
    rewrite piu_zz_inPn_1024_860.
    rewrite piu_zz_inPn_1024_859.
    rewrite piu_zz_inPn_1024_858.
    rewrite piu_zz_inPn_1024_857.
    rewrite piu_zz_inPn_1024_856.
    rewrite piu_zz_inPn_1024_855.
    rewrite piu_zz_inPn_1024_854.
    rewrite piu_zz_inPn_1024_853.
    rewrite piu_zz_inPn_1024_852.
    rewrite piu_zz_inPn_1024_851.
    rewrite piu_zz_inPn_1024_850.
    rewrite piu_zz_inPn_1024_849.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2594-L2614 (assert Hb75) *)
Lemma piu_zz_hb_1024_75 : piu_zz_zprod_seg 1024%nat (512%nat + 320%nat) 16%nat = ((if zz_in_Pn 1024 833%nat then Z.of_nat 833%nat else 1%Z) * ((if zz_in_Pn 1024 834%nat then Z.of_nat 834%nat else 1%Z) * ((if zz_in_Pn 1024 835%nat then Z.of_nat 835%nat else 1%Z) * ((if zz_in_Pn 1024 836%nat then Z.of_nat 836%nat else 1%Z) * ((if zz_in_Pn 1024 837%nat then Z.of_nat 837%nat else 1%Z) * ((if zz_in_Pn 1024 838%nat then Z.of_nat 838%nat else 1%Z) * ((if zz_in_Pn 1024 839%nat then Z.of_nat 839%nat else 1%Z) * ((if zz_in_Pn 1024 840%nat then Z.of_nat 840%nat else 1%Z) * ((if zz_in_Pn 1024 841%nat then Z.of_nat 841%nat else 1%Z) * ((if zz_in_Pn 1024 842%nat then Z.of_nat 842%nat else 1%Z) * ((if zz_in_Pn 1024 843%nat then Z.of_nat 843%nat else 1%Z) * ((if zz_in_Pn 1024 844%nat then Z.of_nat 844%nat else 1%Z) * ((if zz_in_Pn 1024 845%nat then Z.of_nat 845%nat else 1%Z) * ((if zz_in_Pn 1024 846%nat then Z.of_nat 846%nat else 1%Z) * ((if zz_in_Pn 1024 847%nat then Z.of_nat 847%nat else 1%Z) * (if zz_in_Pn 1024 848%nat then Z.of_nat 848%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_848.
    rewrite piu_zz_inPn_1024_847.
    rewrite piu_zz_inPn_1024_846.
    rewrite piu_zz_inPn_1024_845.
    rewrite piu_zz_inPn_1024_844.
    rewrite piu_zz_inPn_1024_843.
    rewrite piu_zz_inPn_1024_842.
    rewrite piu_zz_inPn_1024_841.
    rewrite piu_zz_inPn_1024_840.
    rewrite piu_zz_inPn_1024_839.
    rewrite piu_zz_inPn_1024_838.
    rewrite piu_zz_inPn_1024_837.
    rewrite piu_zz_inPn_1024_836.
    rewrite piu_zz_inPn_1024_835.
    rewrite piu_zz_inPn_1024_834.
    rewrite piu_zz_inPn_1024_833.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2615-L2635 (assert Hb76) *)
Lemma piu_zz_hb_1024_76 : piu_zz_zprod_seg 1024%nat (512%nat + 304%nat) 16%nat = ((if zz_in_Pn 1024 817%nat then Z.of_nat 817%nat else 1%Z) * ((if zz_in_Pn 1024 818%nat then Z.of_nat 818%nat else 1%Z) * ((if zz_in_Pn 1024 819%nat then Z.of_nat 819%nat else 1%Z) * ((if zz_in_Pn 1024 820%nat then Z.of_nat 820%nat else 1%Z) * ((if zz_in_Pn 1024 821%nat then Z.of_nat 821%nat else 1%Z) * ((if zz_in_Pn 1024 822%nat then Z.of_nat 822%nat else 1%Z) * ((if zz_in_Pn 1024 823%nat then Z.of_nat 823%nat else 1%Z) * ((if zz_in_Pn 1024 824%nat then Z.of_nat 824%nat else 1%Z) * ((if zz_in_Pn 1024 825%nat then Z.of_nat 825%nat else 1%Z) * ((if zz_in_Pn 1024 826%nat then Z.of_nat 826%nat else 1%Z) * ((if zz_in_Pn 1024 827%nat then Z.of_nat 827%nat else 1%Z) * ((if zz_in_Pn 1024 828%nat then Z.of_nat 828%nat else 1%Z) * ((if zz_in_Pn 1024 829%nat then Z.of_nat 829%nat else 1%Z) * ((if zz_in_Pn 1024 830%nat then Z.of_nat 830%nat else 1%Z) * ((if zz_in_Pn 1024 831%nat then Z.of_nat 831%nat else 1%Z) * (if zz_in_Pn 1024 832%nat then Z.of_nat 832%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_832.
    rewrite piu_zz_inPn_1024_831.
    rewrite piu_zz_inPn_1024_830.
    rewrite piu_zz_inPn_1024_829.
    rewrite piu_zz_inPn_1024_828.
    rewrite piu_zz_inPn_1024_827.
    rewrite piu_zz_inPn_1024_826.
    rewrite piu_zz_inPn_1024_825.
    rewrite piu_zz_inPn_1024_824.
    rewrite piu_zz_inPn_1024_823.
    rewrite piu_zz_inPn_1024_822.
    rewrite piu_zz_inPn_1024_821.
    rewrite piu_zz_inPn_1024_820.
    rewrite piu_zz_inPn_1024_819.
    rewrite piu_zz_inPn_1024_818.
    rewrite piu_zz_inPn_1024_817.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2636-L2656 (assert Hb77) *)
Lemma piu_zz_hb_1024_77 : piu_zz_zprod_seg 1024%nat (512%nat + 288%nat) 16%nat = ((if zz_in_Pn 1024 801%nat then Z.of_nat 801%nat else 1%Z) * ((if zz_in_Pn 1024 802%nat then Z.of_nat 802%nat else 1%Z) * ((if zz_in_Pn 1024 803%nat then Z.of_nat 803%nat else 1%Z) * ((if zz_in_Pn 1024 804%nat then Z.of_nat 804%nat else 1%Z) * ((if zz_in_Pn 1024 805%nat then Z.of_nat 805%nat else 1%Z) * ((if zz_in_Pn 1024 806%nat then Z.of_nat 806%nat else 1%Z) * ((if zz_in_Pn 1024 807%nat then Z.of_nat 807%nat else 1%Z) * ((if zz_in_Pn 1024 808%nat then Z.of_nat 808%nat else 1%Z) * ((if zz_in_Pn 1024 809%nat then Z.of_nat 809%nat else 1%Z) * ((if zz_in_Pn 1024 810%nat then Z.of_nat 810%nat else 1%Z) * ((if zz_in_Pn 1024 811%nat then Z.of_nat 811%nat else 1%Z) * ((if zz_in_Pn 1024 812%nat then Z.of_nat 812%nat else 1%Z) * ((if zz_in_Pn 1024 813%nat then Z.of_nat 813%nat else 1%Z) * ((if zz_in_Pn 1024 814%nat then Z.of_nat 814%nat else 1%Z) * ((if zz_in_Pn 1024 815%nat then Z.of_nat 815%nat else 1%Z) * (if zz_in_Pn 1024 816%nat then Z.of_nat 816%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_816.
    rewrite piu_zz_inPn_1024_815.
    rewrite piu_zz_inPn_1024_814.
    rewrite piu_zz_inPn_1024_813.
    rewrite piu_zz_inPn_1024_812.
    rewrite piu_zz_inPn_1024_811.
    rewrite piu_zz_inPn_1024_810.
    rewrite piu_zz_inPn_1024_809.
    rewrite piu_zz_inPn_1024_808.
    rewrite piu_zz_inPn_1024_807.
    rewrite piu_zz_inPn_1024_806.
    rewrite piu_zz_inPn_1024_805.
    rewrite piu_zz_inPn_1024_804.
    rewrite piu_zz_inPn_1024_803.
    rewrite piu_zz_inPn_1024_802.
    rewrite piu_zz_inPn_1024_801.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2657-L2677 (assert Hb78) *)
Lemma piu_zz_hb_1024_78 : piu_zz_zprod_seg 1024%nat (512%nat + 272%nat) 16%nat = ((if zz_in_Pn 1024 785%nat then Z.of_nat 785%nat else 1%Z) * ((if zz_in_Pn 1024 786%nat then Z.of_nat 786%nat else 1%Z) * ((if zz_in_Pn 1024 787%nat then Z.of_nat 787%nat else 1%Z) * ((if zz_in_Pn 1024 788%nat then Z.of_nat 788%nat else 1%Z) * ((if zz_in_Pn 1024 789%nat then Z.of_nat 789%nat else 1%Z) * ((if zz_in_Pn 1024 790%nat then Z.of_nat 790%nat else 1%Z) * ((if zz_in_Pn 1024 791%nat then Z.of_nat 791%nat else 1%Z) * ((if zz_in_Pn 1024 792%nat then Z.of_nat 792%nat else 1%Z) * ((if zz_in_Pn 1024 793%nat then Z.of_nat 793%nat else 1%Z) * ((if zz_in_Pn 1024 794%nat then Z.of_nat 794%nat else 1%Z) * ((if zz_in_Pn 1024 795%nat then Z.of_nat 795%nat else 1%Z) * ((if zz_in_Pn 1024 796%nat then Z.of_nat 796%nat else 1%Z) * ((if zz_in_Pn 1024 797%nat then Z.of_nat 797%nat else 1%Z) * ((if zz_in_Pn 1024 798%nat then Z.of_nat 798%nat else 1%Z) * ((if zz_in_Pn 1024 799%nat then Z.of_nat 799%nat else 1%Z) * (if zz_in_Pn 1024 800%nat then Z.of_nat 800%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_800.
    rewrite piu_zz_inPn_1024_799.
    rewrite piu_zz_inPn_1024_798.
    rewrite piu_zz_inPn_1024_797.
    rewrite piu_zz_inPn_1024_796.
    rewrite piu_zz_inPn_1024_795.
    rewrite piu_zz_inPn_1024_794.
    rewrite piu_zz_inPn_1024_793.
    rewrite piu_zz_inPn_1024_792.
    rewrite piu_zz_inPn_1024_791.
    rewrite piu_zz_inPn_1024_790.
    rewrite piu_zz_inPn_1024_789.
    rewrite piu_zz_inPn_1024_788.
    rewrite piu_zz_inPn_1024_787.
    rewrite piu_zz_inPn_1024_786.
    rewrite piu_zz_inPn_1024_785.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2678-L2698 (assert Hb79) *)
Lemma piu_zz_hb_1024_79 : piu_zz_zprod_seg 1024%nat (512%nat + 256%nat) 16%nat = ((if zz_in_Pn 1024 769%nat then Z.of_nat 769%nat else 1%Z) * ((if zz_in_Pn 1024 770%nat then Z.of_nat 770%nat else 1%Z) * ((if zz_in_Pn 1024 771%nat then Z.of_nat 771%nat else 1%Z) * ((if zz_in_Pn 1024 772%nat then Z.of_nat 772%nat else 1%Z) * ((if zz_in_Pn 1024 773%nat then Z.of_nat 773%nat else 1%Z) * ((if zz_in_Pn 1024 774%nat then Z.of_nat 774%nat else 1%Z) * ((if zz_in_Pn 1024 775%nat then Z.of_nat 775%nat else 1%Z) * ((if zz_in_Pn 1024 776%nat then Z.of_nat 776%nat else 1%Z) * ((if zz_in_Pn 1024 777%nat then Z.of_nat 777%nat else 1%Z) * ((if zz_in_Pn 1024 778%nat then Z.of_nat 778%nat else 1%Z) * ((if zz_in_Pn 1024 779%nat then Z.of_nat 779%nat else 1%Z) * ((if zz_in_Pn 1024 780%nat then Z.of_nat 780%nat else 1%Z) * ((if zz_in_Pn 1024 781%nat then Z.of_nat 781%nat else 1%Z) * ((if zz_in_Pn 1024 782%nat then Z.of_nat 782%nat else 1%Z) * ((if zz_in_Pn 1024 783%nat then Z.of_nat 783%nat else 1%Z) * (if zz_in_Pn 1024 784%nat then Z.of_nat 784%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_784.
    rewrite piu_zz_inPn_1024_783.
    rewrite piu_zz_inPn_1024_782.
    rewrite piu_zz_inPn_1024_781.
    rewrite piu_zz_inPn_1024_780.
    rewrite piu_zz_inPn_1024_779.
    rewrite piu_zz_inPn_1024_778.
    rewrite piu_zz_inPn_1024_777.
    rewrite piu_zz_inPn_1024_776.
    rewrite piu_zz_inPn_1024_775.
    rewrite piu_zz_inPn_1024_774.
    rewrite piu_zz_inPn_1024_773.
    rewrite piu_zz_inPn_1024_772.
    rewrite piu_zz_inPn_1024_771.
    rewrite piu_zz_inPn_1024_770.
    rewrite piu_zz_inPn_1024_769.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.
