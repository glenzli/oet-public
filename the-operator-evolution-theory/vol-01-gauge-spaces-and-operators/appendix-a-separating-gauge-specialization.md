## 附录 A 分离规范空间

在一般规范空间中，即使两个点在所有分量下的距离都为零，它们也未必相同。要从全分量零距进一步判定两点相等，需要对规范族增加分离要求。

按照 § 1.1，**分离规范空间**除满足一般规范空间的公理外，还要求规范族 $\mathcal G=\{d_i\}_{i\in I}$ 满足下述**族分离公理**：对任意 $x,y\in\mathcal X$，

$$
\bigl(\forall i\in I,\ d_i(x,y)=0\bigr)
\quad\Longrightarrow\quad x=y.
$$

本附录沿用正文的距离界与零化半径定义，从映射相等的判定出发，讨论计算纤维与局部零化的点值含义，并将这一联系用于算子复合与网络等价关系。

### A.1 分离性与映射相等

先用全族复合距离集中表达全分量零距。沿用 § 1.2 的子族复合伪度量，当 $J=I$ 时，记

$$
d_I(x,y)=\max_{i\in I}d_i(x,y).
$$

**命题 A.1（全族复合距离的开球与分离性）**：对任意 $x\in\mathcal X$ 与 $r\in(0,+\infty)$，均有

$$
B_I(x,r)
:=
\{y\in\mathcal X:d_I(x,y)<r\}
=
\bigcap_{i\in I}B_i(x,r).
$$

若进一步假设 $\mathcal G$ 分离 $\mathcal X$，则 $d_I$ 是 $\mathcal X$ 上的扩展度量。

**证明**：由于 $I$ 有限，$d_I(x,y)<r$ 当且仅当每个 $d_i(x,y)<r$，故得到开球交式。$d_I$ 已是扩展伪度量；在族分离条件下，

$$
d_I(x,y)=0
\quad\Longleftrightarrow\quad
\forall i\in I,\ d_i(x,y)=0
\quad\Longleftrightarrow\quad
x=y.
$$

故 $d_I$ 是扩展度量。$\square$

> **注（族分离不蕴含单分量分离）**：族分离性不蕴含单个 $d_i$ 的分离性。
>
> **证明**：取 $\mathcal X=\{\bot,a,b\}$，其中三点互异，并取 $I=\{i,k\}$。对每个分量规定自距为 $0$，规定 $\bot$ 与任意非吸收点的距离为 $+\infty$，并由对称性补全反向距离；再令
>
> $$
> d_i(a,b)=0,
> \qquad
> d_k(a,b)=1.
> $$
>
> 这些取值满足三角不等式，因而给出两个扩展伪度量。分量 $d_i$ 不分离 $a,b$，而规范族 $\{d_i,d_k\}$ 由 $d_k(a,b)>0$ 分离该点对；涉及 $\bot$ 的点对则由吸收元隔离分离。因此族分离不蕴含单分量分离。$\square$

族分离性也可逐点用于映射；受限评估则把这些逐点条件汇总为上确界条件。

**推论 A.2（全分量零距与映射相等）**：设 $\mathcal G$ 分离 $\mathcal X$。

**(i)** 对任意集合 $A$ 及映射 $f,g:A\to\mathcal X$，

$$
f=g
\quad\Longleftrightarrow\quad
\forall a\in A,\ \forall i\in I,\ d_i(f(a),g(a))=0.
$$

**(ii)** 对任意 $\phi,\psi\in\mathcal X_{\mathrm{op}}$ 与 $U\subseteq\mathcal X$，

$$
\bigl(\forall i\in I,\quad
d_{\mathrm{op},i}(\phi,\psi)\big|_U=0\bigr)
\quad\Longleftrightarrow\quad
\forall x\in U,\quad \phi(x)=\psi(x).
$$

若进一步有

$$
\emptyset\neq U
\subseteq
\operatorname{dom}(\phi)\cap\operatorname{dom}(\psi),
$$

则上述条件还等价于 $\phi\equiv_U\psi$。

特别地，在 (ii) 的零距与逐点相等关系中取 $U=\mathcal X$，得到

$$
\phi=\psi
\quad\Longleftrightarrow\quad
\forall i\in I,\ d_{\mathrm{op},i}(\phi,\psi)=0.
$$

**证明**：**(i)** 正向由自距为零成立；反向逐点使用族分离性，得到 $f(a)=g(a)$（$a\in A$），再由函数外延性得到 $f=g$。

**(ii)** 非负函数的上确界为零当且仅当它处处为零。因此，

$$
\bigl(\forall i\in I,\quad
d_{\mathrm{op},i}(\phi,\psi)\big|_U=0\bigr)
\quad\Longleftrightarrow\quad
\forall x\in U,\ \forall i\in I,\ d_i(\phi(x),\psi(x))=0.
$$

当 $U=\emptyset$ 时，各受限评估按上确界约定取 $0$，右侧为空真，等价关系仍成立。在 (i) 中取 $A=U$，即得受限算子的逐点相等条件。满足非空公共定义域条件时，局部等价的定义（§ 4.5）再给出 $\phi\equiv_U\psi$。全局结论由 $U=\mathcal X$ 时的逐点相等与函数外延性得到。$\square$

**命题 A.3（算子规范族的分离性继承）**：$\mathcal G_{\mathrm{op}}$ 分离 $\mathcal X_{\mathrm{op}}$ 当且仅当 $\mathcal G$ 分离 $\mathcal X$。

**证明**：先设 $\mathcal G$ 分离。由 推论 A.2 的全局结论，全部 $d_{\mathrm{op},i}(\phi,\psi)$ 为零蕴含 $\phi=\psi$，所以 $\mathcal G_{\mathrm{op}}$ 分离。

反之，设 $\mathcal G_{\mathrm{op}}$ 分离。任取满足 $a\sim_{\mathcal G}b$ 的 $a,b\in\mathcal X$，并取固定非吸收点 $z\in\mathcal X\setminus\{\bot\}$。定义

$$
\phi_a(x)=
\begin{cases}
\bot,&x=\bot,\\
a,&x\ne\bot,
\end{cases}
\qquad
\phi_b(x)=
\begin{cases}
\bot,&x=\bot,\\
b,&x\ne\bot.
\end{cases}
$$

则对所有 $i\in I$，$d_{\mathrm{op},i}(\phi_a,\phi_b)=0$。由 $\mathcal G_{\mathrm{op}}$ 分离得 $\phi_a=\phi_b$；在 $z$ 处取值得到 $a=b$。故 $\mathcal G$ 分离。$\square$

### A.2 算子与网络的点值解释

下面结合相应的算子条件，说明单射性、局部性质与复合的点值含义，最后联系网络的零距商与外延商。

**推论 A.4（分离空间中的 co-Lip 单射判据）**：设 $\mathcal G$ 分离 $\mathcal X$，$\phi\in\mathcal X_{\mathrm{op}}$，$U\subseteq\operatorname{dom}(\phi)$。若存在 $\mathbf K\in\mathscr K(\phi)\big|_U$ 使

$$
K_{j\to j}>0
\qquad(\forall j\in I),
$$

则 $\phi$ 在 $U$ 上单射。

**证明**：任取 $x,y\in U$，设 $\phi(x)=\phi(y)$。如 命题 2.8 的证明所示，co-Lip 不等式及各项非负性给出：对任意 $j\in I$，

$$
0\le K_{j\to j}d_j(x,y)
\le \sum_{i\in I}K_{i\to j}d_i(x,y)
\le d_j(\phi(x),\phi(y))
=0.
$$

最后一个等号由 $\phi(x)=\phi(y)$ 及自距为零得到。由于 $K_{j\to j}>0$，必有 $d_j(x,y)=0$。这对所有 $j\in I$ 成立，再由 $\mathcal G$ 的分离性得 $x=y$。因此 $\phi$ 在 $U$ 上单射。$\square$

**推论 A.5（算子局部性质的点值解释）**：设 $\mathcal G$ 分离 $\mathcal X$，$\phi\in\mathcal X_{\mathrm{op}}$，$U\subseteq\operatorname{dom}(\phi)$。

**(i)** $I_{\mathrm{id}}(\phi\mid U)=I$ 当且仅当 $\phi$ 在 $U$ 上逐点恒等，并且对每个 $i\in I$，都存在 $x,y\in U$ 使 $d_i(x,y)>0$。

**(ii)** 若 $U\neq\emptyset$，则 $\phi$ 在 $U$ 上为常值映射，当且仅当

$$
\forall x,y\in U,\ \forall i\in I,
\quad d_i(\phi(x),\phi(y))=0.
$$

**(iii)** 对任意 $y\in\mathcal X$，

$$
\operatorname{Fib}_{\phi,I}(y\mid U)
=
\phi^{-1}(y)\cap U.
$$

当 $U\neq\emptyset$ 时，随 $y\in\phi(U)$ 变化的这些非空纤维，正是 $U$ 按 $\phi\big|_U$ 的点值原像得到的分划。

因此，对任意基点 $y\in U$ 和 $\mathcal X$ 上的输入扩展伪度量 $d_{\mathrm{in}}$，全分量零化内切半径就是 $\phi$ 在评估域 $U$ 内、相对于 $d_{\mathrm{in}}$ 在 $y$ 附近保持局部常值的半径上确界。

**证明**：

**(i)** 先证必要性。设 $I_{\mathrm{id}}(\phi\mid U)=I$。由恒等分量的定义，对任意 $x\in U$，所有 $i\in I$ 均满足 $d_i(\phi(x),x)=0$，故由族分离性得 $\phi(x)=x$。再固定 $i\in I$。由于 $i\notin I_{\mathrm{const}}(\phi\mid U)$，存在 $x,y\in U$ 使 $d_i(\phi(x),\phi(y))>0$。代入逐点恒等关系，得到

$$
d_i(x,y)=d_i(\phi(x),\phi(y))>0.
$$

再证充分性。设 $\phi$ 在 $U$ 上逐点恒等，并且每个分量在 $U$ 上都存在正距离点对。任取 $i\in I$。对所有 $x\in U$，由自距为零，$d_i(\phi(x),x)=d_i(x,x)=0$；另一方面，按假设选取 $x,y\in U$ 使 $d_i(x,y)>0$，则

$$
d_i(\phi(x),\phi(y))=d_i(x,y)>0.
$$

因此 $i\notin I_{\mathrm{const}}(\phi\mid U)$。结合逐点零距关系，由恒等分量的定义得 $i\in I_{\mathrm{id}}(\phi\mid U)$。由于 $i$ 任意，故 $I_{\mathrm{id}}(\phi\mid U)=I$。

(ii) 取 $x_0\in U$。若所有分量的输出距离均为零，则对任意 $x\in U$，族分离性给出 $\phi(x)=\phi(x_0)$，故 $\phi$ 在 $U$ 上为常值映射。反之，若存在 $z\in\mathcal X$ 使 $\phi(x)=z$ 对所有 $x\in U$ 成立，则由自距为零，各分量的输出距离均为零。

(iii) 对任意 $x\in\mathcal X$，

$$
\begin{aligned}
x\in\operatorname{Fib}_{\phi,I}(y\mid U)
&\Longleftrightarrow x\in U\ \text{且}\ \forall i\in I,\ d_i(\phi(x),y)=0\\
&\Longleftrightarrow x\in U\ \text{且}\ \phi(x)=y.
\end{aligned}
$$

第一个等价由计算纤维的定义及 $d_I=\max_{i\in I}d_i$ 得到，第二个等价由族分离性与自距为零得到。故该纤维恰为 $\phi^{-1}(y)\cap U$。不同 $y\in\phi(U)$ 的原像互不相交，每个原像非空，并且这些原像的并为 $U$，故得到所述分划。

以 $\phi(y)$ 为目标值，将上述纤维等式代入 § 3.3 的零化内切半径定义，即得最后的局部常值半径解释。$\square$

统一的局部常值半径与有限输入覆盖结合，还能控制像点的总数。

**推论 A.6（统一零化半径与有限像）**：设 $\mathcal G$ 分离 $\mathcal X$，$f\in\mathcal X_{\mathrm{op}}$，$\varnothing\ne U\subseteq\operatorname{dom}(f)$。取有限正数 $r$，并设

$$
\underline{r}^{\mathrm N}_{f,d_I,I}\big|_U\ge r.
$$

若有限集 $S\subseteq U$ 满足

$$
U\subseteq\bigcup_{s\in S}B_I(s,r),
$$

则

$$
f(U)=f(S).
$$

特别地，若 $\mathcal N_I(r,U)<+\infty$，则 $f(U)$ 有限，且

$$
|f(U)|\le\mathcal N_I(r,U).
$$

**证明**：先证距离小于 $r$ 的任意两点具有相同像值。任取 $x,y\in U$，若 $d_I(x,y)<r$，则

$$
d_I(x,y)<r\le\underline{r}^{\mathrm N}_{f,d_I,I}\big|_U
\le r^{\mathrm N}_{f,d_I,I}(y\mid U).
$$

由 § 3.3 的上确界定义，存在有限正半径 $t>d_I(x,y)$，满足

$$
B_I(y,t)\cap U\subseteq\operatorname{Fib}_{f,I}(f(y)\mid U).
$$

否则所有满足该包含条件的有限正半径都不超过 $d_I(x,y)$，其上确界也不超过 $d_I(x,y)$，与前述严格不等式矛盾。由于 $x\in B_I(y,t)\cap U$，故 $d_I(f(x),f(y))=0$，再由族分离性得 $f(x)=f(y)$。

现取题设的有限中心集 $S$。对任意 $x\in U$，由覆盖条件可选取 $s\in S$ 使 $d_I(x,s)<r$，因而 $f(x)=f(s)$。这说明 $f(U)\subseteq f(S)$；反向包含由 $S\subseteq U$ 得到，故 $f(U)=f(S)$。由于 $S$ 有限，$f(U)$ 也有限，并有 $|f(U)|=|f(S)|\le |S|$。

最后，若 $\mathcal N_I(r,U)<+\infty$，则至少存在一个有限内覆盖。所有这类覆盖的中心数构成非空自然数集，故有最小元。按 § 1.2 的定义，可取中心集 $S_0$ 使 $|S_0|=\mathcal N_I(r,U)$；应用刚才的结论，得到 $|f(U)|\le |S_0|=\mathcal N_I(r,U)$。$\square$

一旦中间像点在全部分量上零距，族分离性便给出点相等；后续复合直接保持这种相等。

**推论 A.7（分离规范下的链级零距传播）**：沿用 命题 4.1 的算子链与轨迹记号，取 $x,x'\in U_1\subseteq\operatorname{dom}(c_k)$。若 $\mathcal G$ 分离 $\mathcal X$，且对某个 $m\in\{0,\ldots,k\}$ 有

$$
d_i(x_m,x'_m)=0
\qquad(\forall i\in I),
$$

则

$$
x_r=x'_r
\qquad(m\le r\le k).
$$

特别地，$c_k(x)=c_k(x')$，终点在全部分量上零距。该结论无须为后续算子另给 Lip 证书。

**证明**：族分离性给出 $x_m=x'_m$。对 $m\le r\le k$，在两边复合同一个后缀 $\phi_r\circ\cdots\circ\phi_{m+1}$（$r=m$ 时为空复合），即得 $x_r=x'_r$。终点零距再由自距为零得到。$\square$

对网络应用映射相等的判定，可以把全部外延网络伪度量给出的零距商与正文的外延商联系起来。

**推论 A.8（网络零距商与外延商的一致性）**：若 $\mathcal G$ 分离 $\mathcal X$，则对任意 $\mathcal N_1,\mathcal N_2\in\mathcal X_{\mathrm{net}}$，

$$
\bigl(\forall i\in I,\quad
d_{\mathrm{net},i}^{\mathrm{op}}(\mathcal N_1,\mathcal N_2)=0\bigr)
\quad\Longleftrightarrow\quad
\mathcal N_1\sim_{\mathrm{op}}\mathcal N_2.
$$

因此零距商与外延商相同，并具有 命题 5.5 给出的算子读出双射及逐分量距离对应；商上的距离与代表元选择无关。

**证明**：由外延网络伪度量的定义和 推论 A.2，

$$
\bigl(\forall i\in I,\quad
d_{\mathrm{net},i}^{\mathrm{op}}(\mathcal N_1,\mathcal N_2)=0\bigr)
\quad\Longleftrightarrow\quad
\phi_{\mathcal N_1}=\phi_{\mathcal N_2}
\quad\Longleftrightarrow\quad
\mathcal N_1\sim_{\mathrm{op}}\mathcal N_2.
$$

两种关系相同，故可直接应用 命题 5.5 的商结论；等价代表元具有相同外延算子，也就给出相同的距离值。$\square$

族分离性使全分量计算纤维成为点值原像，使全分量零化半径具有局部常值半径的解释。在全族距离下，统一的正零化半径结合相同尺度的有限内覆盖，还能控制像点的总数。对于网络，全分量零距与外延算子相等对应，零距商因而与外延商一致；外延相同的网络仍可具有不同的节点与路径结构。

这些点值解释依赖规范族整体的分离性，单个分量仍可能不分离点，距离也仍允许取无穷值。附录 B 进一步引入有限维实坐标结构，研究相应的定量性质。

### A.3 习题

**习题 A.1（正 co-Lip 通道与单射性）**：设规范族 $\mathcal G$ 分离 $\mathcal X$，$\varnothing\ne U\subseteq\operatorname{dom}(\phi)$，且 $\mathbf K\in\mathscr K(\phi)\big\vert_U$。

**(i)** 若每个输入分量至少有一个正的输出通道，即

$$
\forall i\in I,\quad \exists j\in I,\quad K_{i\to j}>0,
$$

证明 $\phi\big\vert_U$ 在 $U$ 上单射，并说明 推论 A.4 的正对角条件是上述条件的特例。这里不要求所选的输出分量 $j$ 彼此不同。

**(ii)** 在 $\mathcal X=\mathbb R^2\sqcup\{\bot\}$ 上取坐标规范族，令 $\phi(s,t)=(t,s)$，$\phi(\bot)=\bot$，$U=\mathbb R^2$。验证

$$
\mathbf K=\begin{pmatrix}0&1\\1&0\end{pmatrix}
$$

是合法的 co-Lip 矩阵。再证明任意合法 co-Lip 矩阵的两个对角条目都为零，说明正对角条件不是单射性的必要条件。

**(iii)** 在 $\mathcal X=\mathbb R\sqcup\{\bot\}$ 上取单分量规范：实数之间使用通常距离，$\bot$ 与每个实数的距离为 $+\infty$。令 $\psi(x)=x^2$（$x\in\mathbb R$）、$\psi(\bot)=\bot$，$V=[0,1]$。证明 $\psi\big|_V$ 单射，但 $V$ 上唯一合法的 co-Lip 常数是 $K=0$。据此判断 **(i)** 的正通道条件是否也是单射性的必要条件。

**习题 A.2（有限像结论的条件）**：在 $\mathcal X=\mathbb R\sqcup\{\bot\}$ 上取单分量规范 $d$：实数之间使用通常距离，$\bot$ 与每个实数的距离为 $+\infty$。令 $f$ 为恒等算子。

**(i)** 取 $U=\{1/n:n\in\mathbb N_{\ge1}\}$。计算各点的零化半径 $r^{\mathrm N}_{f,d,I}(1/n\mid U)$ 及统一零化半径。证明对每个有限正数 $r$ 都有 $\mathcal N_I(r,U)<+\infty$，而 $f(U)$ 仍为无限集。

**(ii)** 取 $V=\mathbb N_{\ge1}$。计算 $\underline{r}^{\mathrm N}_{f,d,I}\big|_V$ 与 $\mathcal N_I(1,V)$，并说明 $f(V)$ 是否有限。

根据这两个例子，分别说明 推论 A.6 中的统一正半径条件为什么不能只要求逐点为正，以及同一半径下的有限覆盖条件为什么不能省略。

**习题 A.3（无穷零化半径的作用范围）**：设 $\mathcal G$ 分离 $\mathcal X$，$f\in\mathcal X_{\mathrm{op}}$，$\varnothing\ne U\subseteq\operatorname{dom}(f)$。

**(i)** 证明

$$
\underline{r}^{\mathrm N}_{f,d_I,I}\big|_U=+\infty
\quad\Longleftrightarrow\quad
\forall x,y\in U,\quad
d_I(x,y)<+\infty\Longrightarrow f(x)=f(y).
$$

据此证明：若 $U$ 中任意两点的 $d_I$ 距离有限，且上述统一零化半径为 $+\infty$，则 $f\big|_U$ 为常值映射。这里是否需要 $U$ 的直径有限？

**(ii)** 取 $\mathcal X=\{\bot,a,b\}$，其中三点互异。令单分量距离在相同点间为 $0$、不同点间为 $+\infty$，$f$ 为恒等算子，$U=\{a,b\}$。验证该规范满足族分离性，并计算统一零化半径，说明 **(i)** 中有限点对距离的条件不能删去。可与 命题 3.8 的反例对照。
