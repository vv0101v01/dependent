# 依賴類型論（Dependent Type Theory）全棧十四模組公理與演算法系統

本儲存庫以 **MoonBit（`moonc v0.10.20`）** 完整實作涵蓋兩階段共 **十九大依賴類型論核心概念** 之形式化公理推導與高效演算法引擎：

- **第一階段十大基礎概念（`M1..M7`）**：
  1. 類型（Type）、2. 項（Term）、3. 判斷（Judgment）、4. 上下文（Context）、5. 依賴函數類型（$\Pi$-Type）、6. 依賴乘積類型（$\Sigma$-Type）、7. 宇宙（Universe $\mathcal{U}_i$）、8. 累積宇宙（Cumulative Universe $\mathcal{U}_i \preceq \mathcal{U}_j, \Downarrow_i / \Uparrow_i$）、9. 柯里-霍華德對應（Curry-Howard Correspondence）、10. 命題即類型（Propositions-as-Types）。
- **第二階段九大進階概念（`M8..M14`）**：
  11. 歸納-遞歸類型（Inductive-Recursive Types）、12. 歸納-歸納類型（Inductive-Inductive Types）、13. 嚴格正歸納類型（Strictly Positive Inductive Types）、14. 共同代數與無窮流（Coalgebras & Infinite Streams）、15. 仿射與量化類型（Affine & Quantitative Types, QTT）、16. 依賴多型性（Dependent Polymorphism）、17. 隱含參數重寫（Implicit Argument Elaboration & Rewriting）、18. 型別強制轉換（Coercive Subtyping）、19. 結構型別與名義型別（Structural vs Nominal Types）。

系統以 **全域公理——伽羅瓦對應（Galois Correspondence）** 與 **局部公理——邏輯消元（Logical Elimination）** 為雙核心綱領，先建構八個零外部依賴之獨立基礎模組（`m1..m4`, `m8..m11`），再透過範疇論組合子（Kan 擴張、Grothendieck 纖維化與層黏合、纖維積與融合推出、Monad 分配律、張量—直和對偶、半直積、Operad、64-bit Chu 空間、Morita 等價、局部化分數、短正合序列與博弈策略合成）融合為六個跨層橋接與總成模組（`m5..m7`, `m12..m14`）。

---

## 一、工作區已獲得之核心公理與跨模組定理體系

1. **全域公理 G1（多層次伽羅瓦對應體系）**：
   - **Chu 語法—語義與始代數—終共同代數對偶（`m6`, `m12`）**：64-bit 位元壓縮矩陣實作 $T \subseteq s(S) \iff S \subseteq t(T)$ 與自對偶轉置 $(C^\perp)^\perp = C$。
   - **代數宇宙約束—賦值反駁對偶（`m2`）**：將全稱語義蘊涵 $\Psi \models A \le B$ 化約為差分圖正權環存在性判定。
   - **量化資源半環殘差伴隨（`m10`）**：`Grade::residuated_sub` 精確計算滿足供給包攝 $(\text{used} + r) \preceq \text{budget}$ 之最小剩餘資源階。
   - **Kan 三元伴隨與遺忘—品牌伴隨（`m5`, `m11`）**：顯示投影三元伴隨 $\Sigma_\pi \dashv \pi^* \dashv \Pi_\pi$（滿足 Beck-Chevalley 同構）以及名義型別至結構型別之受控遺忘伴隨 `Unbrand`。
2. **局部公理 L1（多層次邏輯消元與正規化體系）**：
   - **證明切消元與迂迴消元（`m4`, `m6`）**：Gentzen 序列切消元（`count_cuts == 0`）與自然演繹 $\beta$-正規化構成嚴格交換圖，並驅動博弈策略內部對話隱藏。
   - **零階量化抹除與認證見證提取（`m4`, `m10`, `m13`）**：同時支援邏輯無關證明抹除（$\forall\exists$ 純程式提取）與 QTT 零階（`0`-grade）隱含類型參數執行期完全抹除。
   - **模重寫高階模式合一與去森林化消元（`m11`, `m12`）**：Knuth-Bendix 遞減隱含重寫搭配 Miller 線性脊反演／脊修剪消去全部元變數；雙變形 `hylo_deforest` 消去中間代數樹堆積配置；雙模擬局部化消去冗餘自動機狀態。

---

## 二、十四大模組演算法與常數級／多項式級優化總表

| 模組 | 涵蓋概念 | 關鍵演算法與硬體位元／記憶體優化 |
| :--- | :--- | :--- |
| `dtt/m1_syntax_context` | 類型、項、上下文 | 64-bit `occ_mask`/`slot_mask`/`hash64` $O(1)$ 快篩、DAG `SyntaxArena`、顯式 $\sigma$-代換、反擬陣、Operad |
| `dtt/m2_universe_cumul` | 宇宙、累積宇宙 | $(0,+1,\max)$ 標準形、Fuss-Free $\Downarrow_i/\Uparrow_i$、64-bit 可達快篩 + Tarjan SCC + SPFA、Ramsey 分層 |
| `dtt/m3_pi_sigma_types` | 判斷、$\Pi$、$\Sigma$ | Kripke 域求值與 $\eta$-回引 NbE（$O(1)$ `d - 1 - l`）、雙向檢驗、柯里化與 Skolem 選擇同構 |
| `dtt/m4_curry_howard_prop` | 柯里-霍華德、命題即類型 | 公式$\leftrightarrow$類型雙向同構、Squash 守衛、Gentzen 切消元、CPS 古典合成、認證抹除提取 |
| `dtt/m5_fibration_kan` | 纖維化、Kan 擴張、層黏合 | 劈裂重索引、$\Sigma/\Pi$ 左右 Kan 擴張、語境纖維積／理論推出、Beck-Chevalley 檢驗 |
| `dtt/m6_chu_galois_bridge` | Chu 對偶、Morita、局部化、博弈 | 64-bit Chu 空間、M4$\to$M3 統一索引編譯器、張量—直和分配、Monad 分配律、局部化屋頂 |
| `dtt/m7_unified_kernel` | 第一階段大一統核心 | 累積／非累積雙模態認證、語境反擬陣半直積、伸縮短正合序列分裂截面合成 |
| `dtt/m8_inductive_family` | 嚴格正歸納、IR、II | 64-bit `sp_param_mask` 巢狀稀疏參數化、Dybjer-Setzer IR 同時解碼、II 遞歸-遞歸消元、$W$-摺疊 |
| `dtt/m9_coalgebra_stream` | 共同代數與無窮流 | 迭代安全無窮流、Cauchy 卷積與導數、餘模式字典樹、時鐘守護信用、並查集 $O(N\alpha(N))$ 無限雙模擬 |
| `dtt/m10_affine_quant_types` | 仿射與量化類型 (QTT) | 四元半環殘差、單一 `UInt64` SWAR 32 變數資源向量、乘性 $\Sigma_\pi$ 與加性 $A \with B$、零階抹除 |
| `dtt/m11_polymorphism_coercion_nom` | 依賴多型、隱含重寫、強制轉換、結構／名義 | 模重寫 Miller 模式合一與脊修剪、菱形相干強制轉換、12 指令 `popcount64` $O(1)$ 結構紀錄投影、名義品牌隔離 |
| `dtt/m12_initial_final_duality` | 代數—共同代數對偶與局部化 | 代數—共同代數 Chu 空間、去森林化 `hylo`、雙模擬商駐留為 $O(1)$ Arena ID、II$\to$NbE 反射 |
| `dtt/m13_qtt_elaboration_bridge` | 零開銷精化橋與次結構分層 | 隱含參數零階 QTT 編譯、64-bit `m1 & m2`/`m1 \| m2` 結構紀錄推出、BCKW 次結構證明分類 |
| `dtt/m14_phase2_unified_system` | 全棧十九概念總成核心 | 匯流 `M1..M13` 全棧註冊、精化、$O(1)$ 流雙模擬查詢、資源認證與全域不變量遙測 |

---

## 三、根資料夾視角的依賴關係圖

```text
/home/user (moon.work 十四模組工作區)
├── AGENT.md                                  (工程指引與約束規範)
├── Dev.txt                                   (流水式工程記憶台帳)
└── modules/
    ├── m1_syntax_context/         [基礎 I-A] ──┬───────────────────────┐
    ├── m2_universe_cumul/         [基礎 I-A] ──┼───────────────────┐   │
    ├── m3_pi_sigma_types/         [基礎 I-A] ──┼───────────────┐   │   │
    ├── m4_curry_howard_prop/      [基礎 I-A] ──┼───────────┐   │   │   │
    ├── m5_fibration_kan/          [融合 II-A] ◄────────────┼───┴───┴───┤
    ├── m6_chu_galois_bridge/      [融合 II-A] ◄────────────┴───────────┤
    ├── m7_unified_kernel/         [第一階段總成核心] ◄─────────────────┤
    │                                                                   │
    ├── m8_inductive_family/       [基礎 I-B] ──┬───────────┐           │
    ├── m9_coalgebra_stream/       [基礎 I-B] ──┘           ▼           │
    ├── m12_initial_final_duality/ [融合 II-B] ◄────────────┴───────────┤
    │                                                                   │
    ├── m10_affine_quant_types/    [基礎 I-B] ──┬───────────┐           │
    ├── m11_polymorphism_coercion_nom/ [I-B]  ──┘           ▼           │
    ├── m13_qtt_elaboration_bridge/[融合 II-B] ◄────────────┴───────────┤
    │                                                                   │
    └── m14_phase2_unified_system/ [全棧十九概念總成核心 (匯入 M1..M13)] ◄┘
```

---

## 四、工作區建構動線與對外接口

### 全局檢驗與建置動線
1. 格式一致性檢驗：`moon fmt --check`
2. 十四模組全局零警告類型與介面檢驗：`moon check --deny-warn`
3. 全局編譯建置（不使用 `--release`）：`moon build`

### 對外接入接口
- **全棧一體化入口**：引入 `dtt/m14_phase2_unified_system`，透過 `Phase2UnifiedSystem::new(Cumulative | NonCumulative)` 統一存取十九大依賴類型論概念之全部認證與計算管線。
- **模組化獨立入口**：`dtt/m1_syntax_context` 至 `dtt/m13_qtt_elaboration_bridge` 均可作為獨立套件按需組合引用。
