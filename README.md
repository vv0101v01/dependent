# 依賴類型論（Dependent Type Theory）模組化公理與演算法系統

本儲存庫以 **MoonBit（`moonc v0.10.20`）** 實作涵蓋依賴類型論十大核心概念——**類型（Type）、項（Term）、判斷（Judgment）、上下文（Context）、依賴函數類型（$\Pi$-Type）、依賴乘積類型（$\Sigma$-Type）、宇宙（Universe $\mathcal{U}_i$）、累積宇宙（Cumulative Universe $\mathcal{U}_i \preceq \mathcal{U}_j, \Downarrow_i / \Uparrow_i$）、柯里-霍華德對應（Curry-Howard Correspondence）與命題即類型（Propositions-as-Types）**——之完整形式化公理推導與高效演算法引擎。

系統嚴格遵循 **全域公理——伽羅瓦對應（Galois Correspondence）** 與 **局部公理——邏輯消元（Logical Elimination）**，採取「先建立零耦合獨立基礎模組（`m1..m4`），再以範疇極限、Kan 擴張、Grothendieck 纖維化、Chu 空間對偶、半直積與短正合序列融合為大一統認證核心（`m5..m7`）」之兩層工程架構。

---

## 一、資料夾內已獲得之全域與局部公理及核心定理列表

1. **全域公理 G1（語法—語義與約束—賦值伽羅瓦對應）**：
   - 於 `m6_chu_galois_bridge` 中實作為 64-bit 位元壓縮 Chu 空間 $\mathrm{Chu}(\mathsf{Set}, \mathbf{2})$ 之反變伴隨 $T \subseteq s(S) \iff S \subseteq t(T)$ 與自對偶鏡像 $(C^\perp)^\perp = C$。
   - 於 `m2_universe_cumul` 中實作為代數宇宙約束集 $\Psi$ 與整數賦值模型間之伽羅瓦對偶，導出完備正權環反駁蘊涵演算法。
   - 於 `m3_pi_sigma_types` 與 `m5_fibration_kan` 中實作為左右 Kan 擴張三元伴隨鏈 $\Sigma_\pi \dashv \pi^* \dashv \Pi_\pi$、依賴柯里化同構及 Squash 截斷反射伴隨。
2. **局部公理 L1（邏輯消元、迂迴正規化與變數投影消元）**：
   - 於 `m4_curry_howard_prop` 中實作為 Gentzen 序列演算構造性切消元（`count_cuts == 0`）、Prawitz 自然演繹迂迴消元及其嚴格交換圖定理，以及認證證明抹除提取純計算見證。
   - 於 `m2_universe_cumul` 與 `m3_pi_sigma_types` 中實作為無煩擾宇宙小性消元 $\Uparrow_i(\Downarrow_i A) \equiv_\beta A$、私有宇宙變數 Fourier-Motzkin 投影消元及 Kripke NbE $\beta\eta$-正規化。
   - 於 `m1_syntax_context` 與 `m7_unified_kernel` 中實作為單純形語境強化消元與伸縮短正合序列分裂障礙消元。
3. **十大依賴類型論概念完備覆蓋定理**：
   - **類型、項、上下文**（`m1` 64-bit 位元摘要 AST、嚴格化 $\sigma$-代換演算、反擬陣伸縮語境、DAG 雜湊駐留 Arena）；
   - **判斷、$\Pi$-類型、$\Sigma$-類型**（`m3` 雙向合成／檢驗判斷、帶類型中性項 Kripke NbE、依賴柯里化與依賴 Skolem 選擇同構）；
   - **宇宙、累積宇宙**（`m2` $(0,+1,\max)$ 代數宇宙、Sterbac & Sterling 2026 無煩擾小性編解碼 $\Downarrow_i/\Uparrow_i$、Sozeau & Bezem 2025/2026 差分約束求解、Ramsey-Dilworth 偏序分層）；
   - **柯里-霍華德對應、命題即類型**（`m4` 公式 $\leftrightarrow$ 類型雙向同構、Squash 模態消元守衛、切消元交換圖、CPS 古典雙重否定嵌入、$\forall\exists$ 證明抹除提取；`m6`/`m7` 跨體系核心編譯重驗）。

---

## 二、資料夾內已實作之核心演算法列表

| 模組編號與名稱 | 代表演算法 | 關鍵複雜度與位元／記憶體／序列優化 |
| :--- | :--- | :--- |
| `dtt/m1_syntax_context` | 64-bit 位元遮罩 AST、Hash-Consed DAG Arena、顯式 $\sigma$-代換、反擬陣閉包、Operad 嫁接 | $O(1)$ 封閉項判定、`occ_mask` 自由變數查詢、`slot_mask` 插槽查詢與雜湊不等快篩 |
| `dtt/m2_universe_cumul` | 代數宇宙標準形、Fuss-Free 編解碼正規化、64-bit 可達矩陣 + Tarjan SCC + SPFA 求解、伽羅瓦反駁蘊涵、Ramsey-Dilworth 分解 | $O(1)$ 64 變數序快篩；$O(\|V\|+\|E\|)$ 無嚴格不等式線性求解；多項式時間完備蘊涵判定 |
| `dtt/m3_pi_sigma_types` | Kripke 域求值與類型導向 $\eta$-回引 NbE、雙向判斷合成／檢驗、Church-Peano 常數摺疊、依賴柯里化與 Skolem 變換 | $O(1)$ De Bruijn 層級至索引轉換 `d - 1 - l`；閉包環境惰性延遲代換 |
| `dtt/m4_curry_howard_prop` | 邏輯 $\leftrightarrow$ 類型雙向同構、BHK 證明檢驗與 Squash 守衛、Prawitz 正規化、Gentzen 切消元、CPS 古典公理合成、認證抹除提取 | 雙重良基指標（切公式度與推導高度）保證切消元嚴格終止 |
| `dtt/m5_fibration_kan` | Grothendieck 劈裂重索引、$\Sigma/\Pi$ 左右 Kan 擴張、語境拉回／理論推出、Beck-Chevalley 檢驗、層截面黏合、Operad 纖維嫁接 | 嚴格保持代數小性階與 $\beta\eta$-定義相等 |
| `dtt/m6_chu_galois_bridge` | 64-bit Chu 空間與轉置對偶、位元級伽羅瓦伴隨與概念閉包、M4$\to$M3 統一索引編譯器、張量—直和分配、Monad 分配律、Morita、局部化屋頂、博弈切消元 | 單指令級 `UInt64` 位元 `AND`/`NOT` 驗證全域伽羅瓦對應 |
| `dtt/m7_unified_kernel` | 累積／非累積大一統定理認證、端到端柯里-霍華德提取重驗、語境半直積複合、伸縮短正合序列分裂截面合成、全域遙測巡檢 | 全棧 7 模組零警告聯合編譯與多重交叉驗證 |

---

## 三、根資料夾視角的依賴關係圖

```text
/home/user (moon.work 工作區)
├── AGENT.md                      (工程約束規範)
├── Dev.txt                       (開發全紀錄台帳)
├── .github/workflows/ci.yml      (MoonBit 全局零警告 CI 檢驗管線)
└── modules/
    ├── m1_syntax_context/        [獨立基礎模組] ──┬───────────────┬───────────────┐
    ├── m2_universe_cumul/        [獨立基礎模組] ──┼───────────────┼───────────────┤
    ├── m3_pi_sigma_types/        [獨立基礎模組] ──┼───────────────┼───────────────┤
    ├── m4_curry_howard_prop/     [獨立基礎模組] ──┼───────┐       │               │
    │                                              ▼       │       ▼               │
    ├── m5_fibration_kan/         [範疇纖維化融合] ◄───────┼───────┘               │
    │                                              │       ▼                       │
    ├── m6_chu_galois_bridge/     [Chu-Galois 對偶橋] ◄────┴───────────────────────┘
    │                                              │       │
    │                                              ▼       ▼
    └── m7_unified_kernel/        [大一統依賴類型論認證核心]
```

---

## 四、工作區動線及接入與輸出接口

### 工作區建構與驗證動線
1. `moon.work` 統一註冊 `modules/m1_syntax_context` 至 `modules/m7_unified_kernel` 共七個成員模組。
2. 全局格式化檢驗：`moon fmt --check`
3. 全局零警告靜態類型與介面檢驗：`moon check --deny-warn`
4. 全局編譯建置（禁止 `--release`）：`moon build`

### 對外接入與輸出接口
- **高階一體化接入**：引入 `dtt/m7_unified_kernel`，透過 `UnifiedKernel::new(Cumulative | NonCumulative)` 執行依賴類型宣告認證、柯里-霍華德證明消除與計算程式提取、半直積語境變換、短正合序列分裂分析及核心遙測。
- **分層細粒度接入**：可按需獨立引入 `dtt/m1_syntax_context`（語法與 Arena）、`dtt/m2_universe_cumul`（宇宙約束求解器）、`dtt/m3_pi_sigma_types`（雙向 NbE 核心）、`dtt/m4_curry_howard_prop`（切消元與證明提取）、`dtt/m5_fibration_kan`（Grothendieck 纖維化與 Kan 擴張）或 `dtt/m6_chu_galois_bridge`（64-bit Chu 空間與伽羅瓦伴隨）。
