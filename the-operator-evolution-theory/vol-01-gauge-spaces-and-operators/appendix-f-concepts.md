
<a id="oet-5d6d418ef9f66c91"></a>

## 附录 F 核心概念表

本附录按正文次序汇总本卷的主要概念，供回顾与查阅；各条所附引用指向相应的定义或结果。

---

### §1

* **扩展规范空间与规范结构** [[§ 1.1](<01-foundations.md#user-content-oet-b4babd684de7c112>)]：由集合 $\mathcal X$、指定吸收元 $\bot\in\mathcal X$、满足 $\mathcal X\setminus\{\bot\}\neq\emptyset$ 的非吸收部分，以及满足吸收元隔离条件的有限非空扩展伪度量族 $\mathcal G=\{d_i\}_{i\in I}$ 构成的三元组 $(\mathcal X,\mathcal G,\bot)$。
* **吸收元** [[§ 1.1](<01-foundations.md#user-content-oet-b4babd684de7c112>)]：指定空间元素 $\bot \in \mathcal{X}$，规定其与任意非吸收元测距为 $d_i(x, \bot) = +\infty$（$\forall\, x \neq \bot$）。
* **分量伪度量** [[§ 1.1](<01-foundations.md#user-content-oet-b4babd684de7c112>)]：规范结构 $\mathcal{G}$ 中单个的扩展伪度量 $d_i$。
* **开球** [[§ 1.1](<01-foundations.md#user-content-oet-b4babd684de7c112>)]：在分量伪度量 $d_i$ 下，以 $x_0 \in \mathcal{X}$ 为中心、以有限正数 $r\in(0,+\infty)$ 为半径的点集 $B_i(x_0, r) := \{x \in \mathcal{X} \mid d_i(x, x_0) < r\}$。
* **族零距关系** [[§ 1.1](<01-foundations.md#user-content-oet-b4babd684de7c112>)]：若两个点在全部分量伪度量下均为零距，则记 $x\sim_{\mathcal G}y$；该关系在任意扩展规范空间上都是等价关系。
* **族分离性** [[§ 1.1](<01-foundations.md#user-content-oet-b4babd684de7c112>)]：若族零距关系退化为点相等，即 $x\sim_{\mathcal G}y$ 蕴含 $x=y$，则规范族分离；卷 1 正文不默认这一性质，分离条件下的点值强化集中于 [附录 A](<appendix-a-separating-gauge-specialization.md#user-content-oet-afec88a6c1c23422>)。
* **覆盖数** [[§ 1.2](<01-foundations.md#user-content-oet-65d0745eb743dfe2>)]：在 $U$ 中选取中心、以分量伪度量 $d_i$ 的有限正半径 $\varepsilon$ 开球覆盖 $U$ 所需的最少中心数 $\mathcal{N}_i(\varepsilon,U)$；无有限覆盖时取 $+\infty$，空集取 $0$。
* **度量熵** [[§ 1.2](<01-foundations.md#user-content-oet-65d0745eb743dfe2>)]：覆盖数的对数 $E_{\varepsilon,i}(U):=\log_2\mathcal N_i(\varepsilon,U)$；空集取 $-\infty$，无有限覆盖时取 $+\infty$。
* **子族复合伪度量** [[§ 1.2](<01-foundations.md#user-content-oet-65d0745eb743dfe2>)]：对非空子指标族 $J \subseteq I$ 定义的复合伪度量 $d_J(x, y) := \max_{j \in J} d_j(x, y)$。
* **算子空间** [[§ 1.3](<01-foundations.md#user-content-oet-57a1dc05727a3772>)]：在扩展规范空间 $\mathcal{X}$ 上保持吸收元、即满足 $\phi(\bot) = \bot$ 的全函数集合构成的幺半群 $\mathcal{X}_{\mathrm{op}}$。其吸收元 $\bot_{\mathrm{op}}$ 是全未定义算子。
* **定义域** [[§ 1.3](<01-foundations.md#user-content-oet-57a1dc05727a3772>)]：算子给出非吸收输出的源点子集，定义为 $\mathrm{dom}(\phi) := \{x \in \mathcal{X} \mid \phi(x) \neq \bot\}$。
* **像集** [[§ 1.3](<01-foundations.md#user-content-oet-57a1dc05727a3772>)]：算子在定义域上的输出点集，定义为 $\mathrm{Im}(\phi) := \phi(\mathrm{dom}(\phi))$。由 $\mathrm{dom}(\phi)$ 排除 $\bot$ 及 $\phi(x) \neq \bot$（$x \in \mathrm{dom}(\phi)$），故 $\bot \notin \mathrm{Im}(\phi)$。
* **诱导算子伪度量** [[§ 1.3](<01-foundations.md#user-content-oet-57a1dc05727a3772>)]：算子空间 $\mathcal{X}_{\mathrm{op}}$ 上的全局扩展伪度量，定义为分量距离 $d_i(\phi(x),\psi(x))$ 在全空间上的上确界 $d_{\mathrm{op},i}(\phi, \psi) := \sup_{x \in \mathcal{X}} d_i(\phi(x), \psi(x))$。它使 $(\mathcal{X}_{\mathrm{op}}, \mathcal{G}_{\mathrm{op}}, \bot_{\mathrm{op}})$ 构成扩展规范空间。
* **受限评估** [[§ 1.3](<01-foundations.md#user-content-oet-57a1dc05727a3772>)]：将算子度量评估限制到任意子集 $U \subseteq \mathcal{X}$ 上的推导工具，定义为 $d_{\mathrm{op},i}(\phi, \psi)\big\vert_U := \sup_{x \in U} d_i(\phi(x), \psi(x))$；空域取 $0$，一般不满足吸收元隔离条件。

### §2

* **Lipschitz 矩阵** [[§ 2.1](<02-operator-bounds.md#user-content-oet-af85899693cc8750>)]：界定算子差异传播上限的非负扩展矩阵 $\mathbf L$，其条目约定为 $(\mathbf L)_{ji}=L_{i\to j}$，满足对一切 $x,y \in \mathrm{dom}(\phi)$ 成立的放缩上限：$d_j(\phi(x), \phi(y)) \leq \sum_{i \in I} L_{i \to j} d_i(x, y)$。其全局合法矩阵集记为 $\mathscr{L}(\phi)$。
* **受限 Lipschitz 矩阵** [[§ 2.1](<02-operator-bounds.md#user-content-oet-af85899693cc8750>)]：在特定定义域子集 $U$ 上成立的 Lipschitz 放缩矩阵，其合法矩阵集记为 $\mathscr{L}(\phi)\big\vert_U$。
* **受限 co-Lipschitz 矩阵** [[§ 2.1](<02-operator-bounds.md#user-content-oet-af85899693cc8750>)]：在非空定义域子集 $U\subseteq\mathrm{dom}(\phi)$ 上界定保距下界传播的非负扩展矩阵 $\mathbf K$，其条目约定为 $(\mathbf K)_{ji}=K_{i\to j}$，满足 $d_j(\phi(x),\phi(y))\geq\sum_{i\in I}K_{i\to j}d_i(x,y)$（$\forall x,y\in U,\ \forall j\in I$），其合法矩阵集记为 $\mathscr{K}(\phi)\big\vert_U$。

* **分量通道** [[§ 2.2](<02-operator-bounds.md#user-content-oet-7fa97eb6e24d5527>)]：分量对 $(i,j)\in I\times I$，表示从输入分量 $d_i$ 到输出分量 $d_j$ 的通道。
* **对角 Lip 证书** [[§ 2.2](<02-operator-bounds.md#user-content-oet-7fa97eb6e24d5527>)]：非对角项均为零的合法 Lip 矩阵。

### §3

* **分量分划** [[§ 3.1](<03-operator-local-degeneracy.md#user-content-oet-273361882c9d8ace>)]：在 $U\subseteq\operatorname{dom}(\phi)$（允许为空）上按常值优先，将指标集 $I$ 划分为常值、恒等与有效分量。输出两两零距的指标归入常值分量；其余输出与输入逐点零距的指标归入恒等分量；剩余指标为有效分量。
* **计算纤维** [[§ 3.2](<03-operator-local-degeneracy.md#user-content-oet-77b9589cc080d4f0>)]：在受限子域 $U\subseteq\operatorname{dom}(\phi)$ 和非空指标子族 $J$ 下，目标点 $y\in\mathcal X$ 在复合测距下的零测距原像集合 $\operatorname{Fib}_{\phi, J}(y \mid U) := \{x \in U \mid d_J(\phi(x), y) = 0\}$。
* **像值因子化** [[命题 3.6](<03-operator-local-degeneracy.md#user-content-oet-6d303a1afa732703>)]：在公共域 $U$ 上将 $\phi_B$ 写为 $T\circ\phi_A$；它存在当且仅当 $\mathcal R_{=}(\phi_A\mid U)\subseteq\mathcal R_{=}(\phi_B\mid U)$。相应零距商上的因子化由 $\mathcal R_{\sim}$ 的包含刻画（[命题 3.7](<03-operator-local-degeneracy.md#user-content-oet-c21391963ef67ef0>)）。
* **零测距纤维预序** [[注](<03-operator-local-degeneracy.md#user-content-oet-b99ec286d2be8e72>)]：以 $\mathcal R_{\sim}(\phi_A\mid U)\subseteq\mathcal R_{\sim}(\phi_B\mid U)$ 定义 $\phi_A\succeq_{\mathrm{fiber},U}\phi_B$，比较同一域上零测距纤维分划的粗细。
* **零化内切半径** [[§ 3.3](<03-operator-local-degeneracy.md#user-content-oet-bb1487a09d8bf151>)]：对非空 $U\subseteq\operatorname{dom}(\phi)$ 与基点 $y\in U$，使 $B_{d_{\mathrm{in}}}(y,r)\cap U$ 内所有点的输出与 $\phi(y)$ 在 $d_{\mathrm{out}}$ 下零距的有限正半径 $r$ 所成集合的上确界，记为 $r^{\mathrm N}_{\phi,d_{\mathrm{in}},d_{\mathrm{out}}}(y\mid U)$；无合法半径时取 $0$。$r^{\mathrm N}_{\phi,i,J}$ 是 $d_{\mathrm{in}}=d_i,d_{\mathrm{out}}=d_J$ 的简写。
* **统一零化半径** [[§ 3.3](<03-operator-local-degeneracy.md#user-content-oet-bb1487a09d8bf151>)]：固定非空评估域 $U\subseteq\operatorname{dom}(\phi)$，对非空基点集合 $A\subseteq U$ 定义 $\underline{r}^{\mathrm N}_{\phi,d_{\mathrm{in}},d_{\mathrm{out}}}(A\mid U) := \inf_{y\in A}r^{\mathrm N}_{\phi,d_{\mathrm{in}},d_{\mathrm{out}}}(y\mid U)$；当 $A=U$ 时简记为 $\underline{r}^{\mathrm N}_{\phi,d_{\mathrm{in}},d_{\mathrm{out}}}\big\vert_U$。
* **零化矩阵** [[§ 3.3](<03-operator-local-degeneracy.md#user-content-oet-bb1487a09d8bf151>)]：以单通道统一零化半径为行列条目的特征矩阵 $[\mathbf{N}(\phi)\big\vert_U]_{ji} := \underline{r}^{\mathrm N}_{\phi, i, j}\big\vert_U$。它记录受限算子的统一零化半径，与 $\mathbf L$、$\mathbf K$ 的距离上、下界证书作用不同。
* **映射熵差** [[§ 3.6](<03-operator-local-degeneracy.md#user-content-oet-cf9f43f2f47eb03e>)]：对非空 $U\subseteq\mathrm{dom}(\phi)$、非空输入和输出指标子族及有限正精度 $\varepsilon$，在输入覆盖数与输出覆盖数至少一个有限时定义的差 $\Delta E_{\varepsilon,J_{\mathrm{in}},J_{\mathrm{out}}}(\phi\mid U) := E_{\varepsilon,J_{\mathrm{in}}}(U) - E_{\varepsilon,J_{\mathrm{out}}}(\phi(U))$。

* **输入尺度函数** [[§ 3.4](<03-operator-local-degeneracy.md#user-content-oet-83287e414000b50b>)]：在非空输入域上取值于 $\bar{\mathbb R}_+$、随集合包含不减的函数 $\sigma_i$；默认取 $\operatorname{diam}_{d_i}$。
* **阈值分类** [[§ 3.4](<03-operator-local-degeneracy.md#user-content-oet-83287e414000b50b>)]：固定两个有限正阈值 $\tau_\sigma,\tau_{\mathrm N}$；对算子 $f$、非空 $A\subseteq\operatorname{dom}(f)$ 和通道 $(i,j)$，用 $\operatorname{Type}_{f,A}(i,j)\in\{0,1\}^2$ 记录输入尺度 $\sigma_i(A)<\tau_\sigma$ 与统一零化半径 $\underline{r}^{\mathrm N}_{f,i,j}\big\vert_A\geq\tau_{\mathrm N}$ 是否成立；成立取 $1$，否则取 $0$。

### §4

* **算子链** [[§ 4.1](<04-operator-chain-calculus.md#user-content-oet-5a1b95150c3a4df2>)]：算子的有限有序序列 $(\phi_1,\ldots,\phi_k)$，长度为 $k$，其复合算子为 $c_k=\phi_k\circ\cdots\circ\phi_1$。
* **距离向量** [[§ 4.1](<04-operator-chain-calculus.md#user-content-oet-5a1b95150c3a4df2>)]：由算子链各步中间态像点间的伪度量距离组成的扩展非负实数向量 $\mathbf{d}^{(m)}\in\bar{\mathbb R}_+^I$。
* **常系数证书的谱充分判据** [[命题 4.5](<04-operator-chain-calculus.md#user-content-oet-cb1aac0882bde4ae>)]：当同一个有限值 Lip 或 co-Lip 证书在同一不变域上反复使用时，可用矩阵幂和谱半径估计前缀乘积；它只给证书层充分条件，不替代一般长链的前缀乘积分析。

* **代数因式分解** [[§ 4.3](<04-operator-chain-calculus.md#user-content-oet-92938f295a2b0333>)]：将算子表示为幺半群中两个非恒等算子复合的非平凡分解。
* **不可约算子** [[§ 4.3](<04-operator-chain-calculus.md#user-content-oet-92938f295a2b0333>)]：在幺半群中无法进行非恒等代数因式分解的算子。$|\mathcal{X}| \geq 4$ 时，无约束的 $\mathcal{X}_{\mathrm{op}}$ 中不存在不可约算子（[命题 4.6](<04-operator-chain-calculus.md#user-content-oet-a09c6a96d9cd476a>)）。
* **无约束代数分解边界** [[命题 4.6](<04-operator-chain-calculus.md#user-content-oet-a09c6a96d9cd476a>)]：当底集至少有四个点时，保持吸收元的全体自映射均可写成两个非恒等因子的复合；三点底集上的非吸收点对换给出不可约边界。这不推出受限网络加细的终止性或不可约表示的存在性。
* **域限制算子** [[§ 4.4](<04-operator-chain-calculus.md#user-content-oet-e84832eedce36d68>)]：通过吸收元 $\bot$ 将 $\phi$ 在 $U$ 上的限制补全为全域算子 $\phi\big\vert_U$，所得对象仍属于 $\mathcal X_{\mathrm{op}}$；其复合相容公式使用实际中间像域（[命题 4.7](<04-operator-chain-calculus.md#user-content-oet-a63623c9504af642>)）。
* **定义域分划** [[§ 4.4](<04-operator-chain-calculus.md#user-content-oet-e84832eedce36d68>)]：将非空定义域子集划分为有限个互斥且穷尽非空子集的族。
* **分段算子** [[§ 4.4](<04-operator-chain-calculus.md#user-content-oet-e84832eedce36d68>)]：将多个域限制算子在互斥分划块上进行拼接，并在域外用吸收元 $\bot$ 补全的合成算子。
* **局部等价** [[§ 4.5](<04-operator-chain-calculus.md#user-content-oet-a1caa879309ff2e3>)]：对非空 $U\subseteq\mathrm{dom}(\phi)\cap\mathrm{dom}(\psi)$，若两个算子在 $U$ 上逐点相等，则记 $\phi\equiv_U\psi$。
* **实际输入域序列** [[§ 4.1](<04-operator-chain-calculus.md#user-content-oet-5a1b95150c3a4df2>)]：从非空 $U_1\subseteq\operatorname{dom}(c_k)$ 出发，按 $U_{m+1}=\phi_m(U_m)$ 生成的序列；各步输入域均包含于相应算子的定义域，末项为最终像集。

### §5

* **算子转移图** [[§ 5.1](<05-operator-networks.md#user-content-oet-86752cb60c8e01e3>)]：有限有向图上的局域算子与边域数据；它记录带节点标签的一步转移关系，但不单独给出 $\mathcal X$ 上的外延算子。
* **转移图求值轨迹** [[§ 5.1](<05-operator-networks.md#user-content-oet-86752cb60c8e01e3>)]：由带节点标签状态 $(\beta_s,x_s)$ 组成的非空有限序列，从合法初始状态出发，沿图中的边逐步满足 $x_{s+1}=f_{\beta_s}(x_s)\in D_{\beta_s\to\beta_{s+1}}$。
* **终止域与终止求值轨迹** [[§ 5.1](<05-operator-networks.md#user-content-oet-86752cb60c8e01e3>)]：节点 $\beta$ 的终止域 $T_\beta$ 是 $f_\beta(U_\beta)$ 中未进入任何后继边域的部分；终止求值轨迹在末端节点输出落入终止域时结束。
* **算子网络** [[§ 5.1](<05-operator-networks.md#user-content-oet-86752cb60c8e01e3>)]：由算子转移图加入口输入分划构成，出边转移域互斥，每个输入具有长度统一有界的终止求值轨迹，且每个节点都被某个输入的轨迹经过。
* **网络外延算子** [[§ 5.1](<05-operator-networks.md#user-content-oet-86752cb60c8e01e3>)]：算子网络在初始域 $U$ 上由唯一终止求值轨迹确定，域外取 $\bot$ 后得到 $\phi_{\mathcal{N}}\in\mathcal{X}_{\mathrm{op}}$，且 $\mathrm{dom}(\phi_{\mathcal{N}})=U$。
* **算子网络对象空间** [[§ 5.2](<05-operator-networks.md#user-content-oet-f4f084a4606187ed>)]：$\mathcal{X}_{\mathrm{net}}$ 表示 $\mathcal{X}$ 上节点集为某个有限编号集 $[n]$ 的非空输入网络以及唯一空网络构成的集合。任意有限标签表示须先选定编号编码；对象空间不预先取重标记同构商。
* **无环算子网络对象子空间** [[引理 5.18](<05-operator-networks.md#user-content-oet-13bcaf7893e917fe>)]：$\mathcal X_{\mathrm{net}}^{\mathrm{dag}}$ 表示由无环算子网络和空网络组成的子空间；只有使用节点不重复、深度由节点数控制或无环展开时才显式加入无环条件。
* **网络读出映射** [[§ 5.2](<05-operator-networks.md#user-content-oet-f4f084a4606187ed>)]：从算子网络对象子集到某个集合 $P$ 的映射，用于记录外延、路径分段、标记分段等网络层数据。
* **同外延类** [[命题 5.5](<05-operator-networks.md#user-content-oet-1fb1b80c5f14f459>)]：与固定网络具有相同外延算子的全部有限网络表示所成的等价类 $[\mathcal N]$。
* **外延不变读出的商因子化** [[推论 5.6](<05-operator-networks.md#user-content-oet-53884ec89a20d006>)]：在同外延网络上取相同值的读出唯一通过外延商因子化。
* **可达路径前缀集** [[§ 5.3](<05-operator-networks.md#user-content-oet-374f884cd4d69e88>)]：可达完整路径的全部非空前缀组成的有限集合 $\operatorname{Pref}(\mathcal N)$；同一节点可以在前缀中重复出现。
* **网络路径** [[§ 5.3](<05-operator-networks.md#user-content-oet-374f884cd4d69e88>)]：有限算子网络中，点 $x\in U$ 的唯一终止求值轨迹确定的有限节点序列 $p(x)$。
* **路径域** [[§ 5.3](<05-operator-networks.md#user-content-oet-374f884cd4d69e88>)]：具有同一网络路径 $p$ 的初始点集合 $U_p$，构成 $U$ 的分划。
* **路径前缀发生** [[§ 5.3](<05-operator-networks.md#user-content-oet-374f884cd4d69e88>)]：以可达前缀 $q$ 区分一次局部调用及其到达历史，$D_q^{\mathrm{in}}$ 与 $D_q^{\mathrm{out}}$ 分别记录该前缀末节点作用前后的点值集合；$U[q\ast]$ 则是产生该前缀的初始输入集合。
* **路径分段表达 / 路径分段读出** [[§ 5.3](<05-operator-networks.md#user-content-oet-374f884cd4d69e88>)]：由路径域分划与路径复合族决定的未标记分段数据 $\Gamma_{\mathrm{path}}(\mathcal N)=\{U_p:c_p\}_{p\in\mathcal P(\mathcal N)}$；相应的网络读出映射记为 $\Gamma_{\mathrm{path}}$。
* **网络表示** [[§ 5.2](<05-operator-networks.md#user-content-oet-f4f084a4606187ed>)]：输入域为非空集合 $U$ 的算子网络 $\mathcal N$ 表示算子 $\phi$ 在该域上的取值，要求 $\phi_{\mathcal N}\equiv_U \phi$。
* **节点实际输入域** [[§ 5.4](<05-operator-networks.md#user-content-oet-adb38f8458662a70>)]：节点 $\beta$ 在真实求值过程中被调用的输入集合 $U_\beta^{\mathrm{eff}}$，由所有以 $\beta$ 为末节点的可达前缀的当前输入域取并得到。
* **有效约化网络** [[§ 5.4](<05-operator-networks.md#user-content-oet-adb38f8458662a70>)]：把每个节点算子限制到其节点实际输入域，并只保留实际经过的边域与终止输出后得到的网络 $\mathcal N^{\mathrm{eff}}$；它与原网络外延等价。
* **标记分段算子表达 / 标记分段读出** [[§ 5.4](<05-operator-networks.md#user-content-oet-adb38f8458662a70>)]：在路径域分划下，把每个路径片的复合写成带节点标签的逐步复合因子后得到的分段算子表达 $\Gamma_{\mathrm{tag}}(\mathcal N)$；相应的网络读出映射记为 $\Gamma_{\mathrm{tag}}$。
* **外延等价与有效等价** [[§ 5.4](<05-operator-networks.md#user-content-oet-adb38f8458662a70>)]：外延等价只要求网络外延算子在同一输入域上局部等价；有效等价要求标记分段算子表达同构，因而保留路径分段复合、因子标签以及实际发生输入上的因子局部等价。
* **网络加细** [[§ 5.6](<05-operator-networks.md#user-content-oet-eddd1f2d0a9d3528>)]：在不改变网络外延算子局部等价行为的条件下，对网络节点进行输入域细分或对局域算子进行代数分解的结构扩展操作。
* **允许加细规则族** [[§ 5.6](<05-operator-networks.md#user-content-oet-eddd1f2d0a9d3528>)]：指定哪些节点域加细、代数加细及其 L/K/N 比较条件被允许的一步加细关系族，记为 $\mathcal N\to_R\mathcal N'$。
* **不可约网络表示** [[§ 5.6](<05-operator-networks.md#user-content-oet-eddd1f2d0a9d3528>)]：在给定加细规则族 $R$ 下不可再作一步允许加细的网络表示 $\mathcal N$；若它表示 $\phi$ 在 $U$ 上的取值，则满足 $\phi_{\mathcal N}\equiv_U\phi$。其存在性与唯一性须另行讨论。
* **前缀扩展** [[§ 5.7](<05-operator-networks.md#user-content-oet-247e7abff05fe1ff>)]：在算子网络前端加入一个新的入口节点 $\alpha$，使扩展网络满足 $\phi_{\mathcal{N}_\varphi}=(\phi_{\mathcal{N}}\circ\varphi)\big|_{D_0}$。

* **前缀发生统一零化半径** [[§ 5.5](<05-operator-networks.md#user-content-oet-4b1389b158d2780e>)]：对路径前缀发生 $q$，在当前输入域 $D_q^{\mathrm{in}}$ 上读取局部算子 $f_q$ 的通道统一零化半径 $\underline{r}^{\mathrm N}_q(i,j)$。
* **路径阈值序列** [[§ 5.5](<05-operator-networks.md#user-content-oet-4b1389b158d2780e>)]：按路径次序读取各前缀发生域上的阈值分类 $\operatorname{Type}_q=\operatorname{Type}_{f_q,D_q^{\mathrm{in}}}$，所得有限序列；固定通道后得到相应的二元标签序列。

### 附录 A

* **全族复合度量** [[§ A.1](<appendix-a-separating-gauge-specialization.md#user-content-oet-5ddb4141bb0d9204>)]：取全部指标 $I$ 得到的复合伪度量 $d_I=\max_{i\in I}d_i$；在族分离条件下，它把全分量零测距精确识别为点相等。
* **全分量零距与映射相等** [[推论 A.2](<appendix-a-separating-gauge-specialization.md#user-content-oet-d855ee3b07cdd0e9>)]：在分离规范空间中，全分量逐点零距等价于映射相等；两个算子在 $U$ 上逐点相等，也等价于全部受限算子伪度量为零。
* **全分量恒等、常值与纤维** [[推论 A.5](<appendix-a-separating-gauge-specialization.md#user-content-oet-1d4e90ad08791619>)]：族分离性把全分量恒等、常值及计算纤维联系到相应的点值关系。全分量恒等还要求每个分量在限制域上存在正距离点对，以符合常值优先的分量分划。
* **算子规范族的分离性继承** [[命题 A.3](<appendix-a-separating-gauge-specialization.md#user-content-oet-71c78680ea301971>)]：诱导算子规范族分离算子空间，当且仅当原规范族分离点空间。
* **正对角 co-Lip 单射判据** [[推论 A.4](<appendix-a-separating-gauge-specialization.md#user-content-oet-014c35c64a75152a>)]：在分离规范空间中，全体正对角 co-Lip 条目把正文的族零距反射结论提升为限制域上的点值单射性。
* **全分量零距传播** [[推论 A.7](<appendix-a-separating-gauge-specialization.md#user-content-oet-77a0d1aa13ceb857>)]：链的某个中间状态在全部规范分量上零距时，分离性把它提升为中间点相等，因而无需后续 Lip 证书即可保持后续轨迹相等。
* **网络零距商** [[推论 A.8](<appendix-a-separating-gauge-specialization.md#user-content-oet-8c3b9b6221a633b6>)]：在分离规范空间中，网络对象的全分量外延零距关系与外延算子相等关系一致，其商通过算子读出逐分量保距地对应算子空间。
* **全分量局部常值半径** [[推论 A.5](<appendix-a-separating-gauge-specialization.md#user-content-oet-1d4e90ad08791619>)]：在分离规范空间中，以全族复合度量读取输出时，零化内切半径是映射在输入伪度量球与评估域 $U$ 的交集上保持点值常值的有限正半径上确界。

* **统一零化半径与有限像** [[推论 A.6](<appendix-a-separating-gauge-specialization.md#user-content-oet-f2de1cf0247fd557>)]：在分离规范空间中，若全族统一零化半径至少为有限正数 $r$，且输入域有半径 $r$ 的有限内覆盖，则全部像点由覆盖中心的像给出，像点数不超过该内覆盖数。

### 附录 B

* **坐标规范族** [[§ B.1](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-f87662457a7d82d4>)]：在 $A\subseteq\mathbb R^n$ 上由各坐标差 $|x_i-y_i|$ 诱导的有限分量伪度量族；其全族复合度量是 $\ell^\infty$ 距离。
* **范数聚合距离** [[§ B.1](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-f87662457a7d82d4>)]：在坐标规范族之上另选范数 $\|\cdot\|_*$ 得到的标量扩展度量 $d_*$；有限维范数等价保证其拓扑与坐标规范拓扑一致，定量常数则依赖范数选择。
* **正交块规范族** [[§ B.3](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-def6ef684420ce10>)]：由有限正交直和分解的各正交投影拉回欧氏距离所成的分量伪度量族；其分量平方和恢复欧氏距离平方，一维标准分解退化为坐标规范族。
* **欧氏覆盖数的维数估计** [[命题 B.4](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-a57e9e873735ed63>)]：$r$ 维仿射子空间中包含于半径 $R$ 球内的非空集合，其内覆盖数不超过 $(1+2R/\varepsilon)^r$；整个欧氏球另有体积下界，线性像的上界则由像空间的维数即秩控制。
* **Jacobi 分量上界证书** [[§ B.2](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-a81f07d81e16c501>)]：在具有连续可微扩展的非空凸评估域上，若各偏导数绝对值的上确界有限，则这些上确界组成坐标 Lip 矩阵，并可按选定范数聚合为标量 Lip 上界。
* **Jacobi 正交块上界证书** [[§ B.3](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-def6ef684420ce10>)]：在具有连续可微扩展的非空凸评估域上，若各 $\sup_{z\in U}\|P_b\circ DF(z)\circ P_a\|_{2\to2}$ 有限，则以它们为条目形成正交块 Lip 矩阵；零块条目给出相应单块扰动的块间解耦。
* **坐标 co-Lip 范数下界** [[§ B.4](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-93bf7093aa284ce2>)]：由逐条目有限的坐标 co-Lip 矩阵逐输入分量取输出条目最大值、再对输入分量取最小值得到的常数，导出 $\ell^\infty$ 及任意等价范数下界；欧氏下界不能反向推出非零坐标 co-Lip 矩阵（[命题 B.10](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-69edb7c1cac5d49b>) 的 (ii)）。
* **非线性微分下界的全局边界** [[命题 B.12](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-3e4095f278f5ea6b>)]：对在包含凸评估域的开邻域上连续可微的映射，Jacobi 二次型的统一正下界通过线段积分给出全局 co-Lip 与受限单射性；仅有点态最小奇异值的一致正下界则不足，存在凸开域上的非单射反例。
* **仿射算子的欧氏双侧界** [[命题 B.11](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-e1bc9665adf4aeca>)]：全空间仿射映射 $F(x)=Tx+b$ 的最优欧氏 Lip 上界与 co-Lip 下界分别等于 $\sigma_{\max}(T)$ 与 $\sigma_{\min}(T)$；任意受限域只继承相应不等式。
* **正交换基不变量** [[命题 B.11](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-e1bc9665adf4aeca>) 的 (ii)]：正交输入、输出换基保持线性映射的奇异值及最优欧氏双侧常数，但一般改变坐标条目绝对值及其非零支撑。
* **输入上界支撑** [[§ B.2](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-a81f07d81e16c501>)]：由所选坐标 Lip 证书的正条目记录进入一个输出分量上界的输入分量；它不判定算子的实际分量依赖关系。支撑基数、最大条目及输入扰动支撑的交叠共同给出稀疏传播上界。
* **行支撑控制的距离上界** [[推论 B.7](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-36ae8406e21d3213>)]：所选坐标 Lip 证书的最大行非零条目数与最大条目之积，给出最大范数下的距离放大上界；若这两个量在不同维数的模型中均有统一上界，则该 Lip 上界也可统一控制。
* **分量形态的导数判据** [[习题 B.6](<appendix-b-finite-dimensional-coordinate-model.md#mb-exercise-oet-ac7cdc1d2ab36d93>)]：对非空开凸域上的连续可微映射，输出坐标常值等价于对应梯度恒为零；输出坐标恒等等价于梯度恒为相应基向量并在一个基点取恒等值。
* **集合的方向空间** [[引理 B.13](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-5327d971cf04c4ca>)]：非空集合 $U$ 的点差张成的线性空间 $W_U$。仿射映射 $F(x)=Tx+b$ 满足 $W_{F(U)}=T(W_U)$；其受限线性作用不依赖域外扩展。
* **仿射零化半径** [[命题 B.14](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-055e3702cf9c3930>) 的 (ii)]：在非空凸域或开域上，采用全族输入、输出距离 $d_I$ 时，仿射映射的零化半径由线性部分在 $W_U$ 上是否为零判定；采用任意输入坐标距离 $d_i$ 与输出坐标距离 $d_j$ 时，由第 $j$ 行在 $W_U$ 上是否为零判定。相应值为 $+\infty$ 或 $0$，且与基点无关；开域中 $W_U=\mathbb R^n$。
* **真实导数通道展开** [[命题 B.15](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-8b08064a80bd8c55>)]：复合导数条目是带符号通道乘积之和，其绝对值由逐条目绝对值矩阵乘积控制；不同真实通道可以相消。
* **逐步扰动传播** [[习题 B.8](<appendix-b-finite-dimensional-coordinate-model.md#mb-exercise-oet-ef39fb9c4b025f07>)]：对逐条目非负有限矩阵下满足 $e^{(m)}\le\mathbf M^{(m)}e^{(m-1)}+r^{(m)}$ 的非负向量递推，用初始扰动的矩阵乘积传播与各步余项的后缀传播之和给出末步扰动上界。

### 附录 C

* **路径 Jacobi 乘积** [[命题 C.1](<appendix-c-finite-dimensional-operator-networks.md#user-content-oet-6de8b6950c13065a>)]：当网络节点局域算子具有连续可微扩展时，固定路径的扩展复合导数等于各节点发生处 Jacobi 矩阵按求值次序的乘积。若路径在点的一个开邻域内保持不变，该导数也是网络外延算子的局部导数。
* **节点发生域导数证书** [[推论 C.3](<appendix-c-finite-dimensional-operator-networks.md#user-content-oet-282a390854b22758>)]：在节点连续可微扩展的定义域内，选取包含实际节点发生输入集的非空凸集；其有限坐标偏导或正交块导数上界沿路径相乘，给出路径域上的 Lip 证书。
* **正交块通路** [[推论 C.2](<appendix-c-finite-dimensional-operator-networks.md#user-content-oet-f8dabd5aec160cd3>)]：路径块导数按中间正交块指标展开；非零块导数要求至少存在一条逐节点非零块通路，但逐步非零的块映射仍可能复合为零，不同通路项也可能相消。
* **线性单元** [[§ C.2](<appendix-c-finite-dimensional-operator-networks.md#user-content-oet-1fc7e6eee4342892>)]：由有限多个仿射等式、严格不等式与非严格不等式共同定义的有限维区域；它对有限交和仿射原像封闭。
* **分片仿射网络** [[命题 C.4](<appendix-c-finite-dimensional-operator-networks.md#user-content-oet-f2b0bcadc14fb5ac>)]：当节点算子仿射且入口片、边域、终止域均为线性单元时，每个路径域是线性单元，网络外延算子在输入域上形成有限分片仿射映射。
* **仿射网络外延的复合封闭性** [[命题 C.5](<appendix-c-finite-dimensional-operator-networks.md#user-content-oet-292cbcc4dd47c8cc>)]：满足线性单元条件的两张仿射网络，在复合有效域上仍可由同类网络表示；复合分片由第一网路径域与第二网路径域的仿射原像取交得到。
* **路径中的变化方向** [[命题 C.6](<appendix-c-finite-dimensional-operator-networks.md#user-content-oet-e4b8f2d657424bba>)]：在仿射网络中，固定完整可达路径后，实际中间像集的方向空间逐步经节点线性部分映射，其维数不增。
* **路径限制秩覆盖上界** [[推论 C.7](<appendix-c-finite-dimensional-operator-networks.md#user-content-oet-c9e4b6fb4f7e4e59>)]：各实际路径输入域有界时，仿射路径像集的内覆盖数由实际路径域上的限制秩、所选扩展的算子范数和路径域半径控制；网络输出内覆盖数再由有限路径求和得到。
* **仿射局域算子的阈值分类** [[命题 C.6](<appendix-c-finite-dimensional-operator-networks.md#user-content-oet-e4b8f2d657424bba>)]：采用坐标规范及有限正阈值时，在仿射节点的非空凸发生域上，阈值标签第一位由输入尺度确定，第二位为 $1$ 当且仅当相应输出行在该发生域的方向空间上为零，即该输出分量在该域上常值。
