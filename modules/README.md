# `modules/`（依賴類型論七大模組群總覽）

本資料夾承載整個依賴類型論工作區之兩層模組化架構：
- **第一層（零外部依賴之獨立基礎模組）**：`m1_syntax_context`、`m2_universe_cumul`、`m3_pi_sigma_types`、`m4_curry_howard_prop`。
- **第二層（範疇組合、對偶橋接與大一統認證核心模組）**：`m5_fibration_kan`、`m6_chu_galois_bridge`、`m7_unified_kernel`。

---

## 一、資料夾內已獲得之定理列表（跨子模組匯總）

1. **M1 語法與語境層**：64-bit 自由變數與插槽位元摘要健全性定理、嚴格化顯式 $\sigma$-代換交換定理、語境反擬陣依賴閉包與單純形面／退化恆等式、有色多範疇 Operad 嫁接結合律定理。
2. **M2 宇宙與累積層**：代數宇宙自由半格標準形定理、無煩擾（Fuss-Free）累積宇宙小性編解碼 $\beta/\eta$-單射定理（Sterbac & Sterling, 2026）、多項式時間差分約束伽羅瓦反駁完備性定理（Sozeau & Bezem, 2025/2026）、宇宙偏序集 Mirsky-Dilworth 與 Erdős-Szekeres / Ramsey 分層界定理。
3. **M3 依賴函數與乘積層**：帶類型中性項 Kripke 語義域正規化（NbE）健全性與 $\beta\eta$-決定性定理（Jiang, Hu, Oliveira, ICFP 2025）、依賴柯里化伴隨同構 $\Sigma \dashv \Pi$ 定理、依賴 Skolem 選擇泛性質同構定理。
4. **M4 柯里-霍華德與命題即類型層**：一階依賴邏輯公式與證明類型雙向同構定理、Squash 截斷命題反射消元安全定理、Gentzen 序列演算切消元主定理（Hauptsatz）與自然演繹 $\beta$-正規化交換圖定理、CPS 古典排中律／Peirce 律構造性嵌入定理、認證證明抹除與 $\forall\exists$ 純程式提取定理。
5. **M5 纖維化與 Kan 擴張層**：Grothendieck 理解纖維化劈裂重索引函子性定理、顯示投影左右 Kan 擴張（$\Sigma_\pi \dashv \pi^* \dashv \Pi_\pi$）實現定理、語境纖維積／理論推出之 Beck-Chevalley 自然同構定理、Grothendieck 覆蓋截面層黏合定理。
6. **M6 Chu 空間與全域伽羅瓦橋接層**：64-bit Chu 空間自對偶鏡像 $(C^\perp)^\perp = C$ 與位元級全域伽羅瓦對應 $T \subseteq s(S) \iff S \subseteq t(T)$ 定理、雙命名空間邏輯至統一依賴核心編譯保持定理、依賴張量—直和分配同構定理、Writer-Squash Monad 分配律定理、Morita 等價定理、右分數局部化屋頂與博弈策略切消元隱藏定理。
7. **M7 大一統核心與同調代數層**：累積／非累積雙模態核心認證健全性定理、端到端柯里-霍華德證明消除與核心重驗定理、語境反擬陣自同構與代換半直積同態定理、依賴伸縮短正合序列零障礙分裂判準定理。

---

## 二、資料夾內已實作之演算法列表

| 子模組資料夾 | 核心演算法族群 | 代表複雜度特徵 |
| :--- | :--- | :--- |
| `m1_syntax_context` | 64-bit `occ_mask`/`slot_mask`/FNV-1a 雜湊建構、DAG 雜湊駐留 Arena、嚴格化 $\sigma$-代換、反擬陣依賴閉包、單純形弱化／強化、Operad 嫁接 | $O(1)$ 封閉性／變數出現／雜湊相等快篩 |
| `m2_universe_cumul` | 代數宇宙標準化、Fuss-Free 小性合成與正規化、Tarjan SCC + SPFA 差分圖求解、伽羅瓦反駁蘊涵判定、Ramsey-Dilworth 鏈／反鏈分解 | $O(1)$ 64 變數可達快篩；多項式時間完備蘊涵判定 |
| `m3_pi_sigma_types` | 閉包語義求值 `eval_tm`、類型導向 $\eta$-回引 `quote_val`、雙向類型合成／檢驗、Church-Peano 常數摺疊、依賴柯里化與 Skolem 雙向變換 | $O(1)$ De Bruijn 層級轉索引 `d - 1 - l` |
| `m4_curry_howard_prop` | 公式 $\leftrightarrow$ 類型雙向編譯、BHK 證明檢驗與 Squash 守衛、Prawitz 迂迴正規化、Gentzen 構造性切消元、CPS 古典公理合成、認證證明抹除提取 | 切秩與公式度良基雙重歸納終止 |
| `m5_fibration_kan` | `SynExpr <-> CoreTm` 雙向函子橋、劈裂笛卡兒重索引、$\Sigma/\Pi$ 左右 Kan 擴張、語境拉回／理論推出、Beck-Chevalley 檢驗、層黏合與 Operad 驗證 | 線性語境偏移與 NbE 語義驗證 |
| `m6_chu_galois_bridge` | 64-bit 位元矩陣 Chu 空間、$O(1)$ 伽羅瓦伴隨與概念閉包、M4$\to$M3 統一索引證明編譯器、張量—直和分配、Monad 分配律、Morita 等價、局部化屋頂、博弈切消元 | 單指令級 `UInt64` 位元遮罩伽羅瓦運算 |
| `m7_unified_kernel` | 雙模態大一統定理認證、端到端邏輯證明提取與重驗、反擬陣自同構與半直積複合、伸縮短正合序列障礙秩與分裂截面合成、全域遙測巡檢 | 跨全棧 7 模組閉環認證 |

---

## 三、資料夾視角的依賴關係圖

```text
                       ┌────────────────────── modules/ ──────────────────────┐
                       │                                                      │
   Layer I (獨立基礎)   │  m1_syntax_context   m2_universe_cumul               │
                       │  m3_pi_sigma_types   m4_curry_howard_prop            │
                       │         │                   │                        │
                       ├─────────┼───────────────────┼────────────────────────┤
                       │         ▼                   ▼                        │
   Layer II (範疇融合)  │  m5_fibration_kan (← m1, m2, m3)                     │
                       │  m6_chu_galois_bridge (← m1, m2, m3, m4)             │
                       │         │                   │                        │
                       │         └─────────┬─────────┘                        │
                       │                   ▼                                  │
                       │  m7_unified_kernel (← m1, m2, m3, m4, m5, m6)        │
                       └──────────────────────────────────────────────────────┘
```

---

## 四、資料夾內動線及接入與輸出接口

### 內部動線
1. 第一層 `m1..m4` 各自擁有獨立 `moon.mod` 且零跨模組耦合，可單獨編譯與驗證。
2. 第二層 `m5` 與 `m6` 透過根目錄 `moon.work` 引入第一層基礎模組，分別完成幾何纖維化／Kan 擴張融合與 Chu-Galois 邏輯對偶橋接。
3. 頂層 `m7_unified_kernel` 匯入 `m1..m6`，對外暴露統一認證核心。

### 接入與輸出接口
- 每個子資料夾皆作為獨立 MoonBit 模組發佈於命名空間 `dtt/<module_name>@0.1.0`，外部調用者可按需單獨接入任一基礎模組，或直接引入 `dtt/m7_unified_kernel` 取得全套大一統 API。
