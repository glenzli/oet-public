
<a id="oet-c208c57dee861c5e"></a>

## 附录 C 有限维算子网络

有限算子网络把输入分配到不同路径；在一条路径内部，局域算子又按顺序复合。本附录用 [附录 B](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-a5195ee5769e4816>) 的有限维工具分别描述这两层结构：先沿固定路径计算导数，展开正交块之间的作用通路，并在实际发生域上取得距离上界；再考察仿射网络的路径单元如何参与复合，以及实际发生域中的变化方向如何沿路径传递，并据此估计输出覆盖。

网络仍按 [§ 5.1](<05-operator-networks.md#user-content-oet-86752cb60c8e01e3>) 定义，路径、路径域与路径复合沿用 [§ 5.3](<05-operator-networks.md#user-content-oet-374f884cd4d69e88>)。

以下取 $n\ge1$、$I=\{1,\ldots,n\}$，并令

$$
\mathcal X
=
\mathbb R^n\cup\{\bot\},
$$

采用 [附录 B](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-a5195ee5769e4816>) 的坐标规范族或一个固定正交块规范族。设 $\mathcal N\in\mathcal X_{\mathrm{net}}$ 为输入域 $U\subseteq\mathbb R^n$ 非空的有限算子网络，节点集为 $V$，节点 $\beta$ 的局域算子为 $f_\beta$，其定义域记为 $U_\beta$。


<a id="oet-ac1e85729aad39ca"></a>

### C.1 路径导数与距离估计

假设对每个节点 $\beta\in V$，存在包含 $U_\beta$ 的开集 $O_\beta\subseteq\mathbb R^n$ 与连续可微映射

$$
F_\beta:O_\beta\to\mathbb R^n,
$$

使

$$
F_\beta\big|_{U_\beta}
=
f_\beta\big|_{U_\beta}.
$$

固定可达路径

$$
p=(\beta_1,\ldots,\beta_r)
\in\mathcal P(\mathcal N)
$$

及 $x\in U_p$。定义路径中间点

$$
x_{p,0}(x)=x,
\qquad
x_{p,s}(x)
=
F_{\beta_s}(x_{p,s-1}(x))
\quad(1\le s\le r),
$$

以及节点发生处的 Jacobi 矩阵

$$
A_{p,s}(x)
:=
DF_{\beta_s}(x_{p,s-1}(x)).
$$

由于 $x\in U_p$，这些中间点与网络求值轨迹的点值相同，并且 $x_{p,s-1}(x)\in U_{\beta_s}\subseteq O_{\beta_s}$。


<a id="oet-6de8b6950c13065a"></a>

**命题 C.1（路径复合的 Jacobi 乘积）**：对任意 $p\in\mathcal P(\mathcal N)$ 与 $x\in U_p$，路径复合

$$
C_p
=
F_{\beta_r}\circ\cdots\circ F_{\beta_1}
$$

在 $x$ 的某个开邻域内良定义，并满足

$$
DC_p(x)
=
A_{p,r}(x)\cdots A_{p,1}(x).
$$

若存在 $x$ 的开邻域 $W$ 使

$$
W\subseteq U_p,
$$

则网络外延算子在 $W$ 上等于 $C_p$，因而

$$
D\bigl(\phi_{\mathcal N}\big|_W\bigr)(x)=DC_p(x),
$$

其中 $\phi_{\mathcal N}\big|_W$ 由 $W\subseteq U_p\subseteq U$ 视为取值于 $\mathbb R^n$ 的局部映射。

**证明**：沿用 [命题 B.15](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-8b08064a80bd8c55>) 的复合求导方法，先说明路径复合在 $x$ 附近良定义。令

$$
V_1=O_{\beta_1},\qquad C_1=F_{\beta_1}.
$$

则 $V_1$ 是包含 $x$ 的开集，且 $C_1$ 在其上连续可微。假设前 $s$ 步复合 $C_s$ 已在包含 $x$ 的开集 $V_s$ 上连续可微，其中 $1\le s<r$。由于

$$
C_s(x)=x_{p,s}(x)\in O_{\beta_{s+1}},
$$

可取

$$
V_{s+1}
=\{y\in V_s:C_s(y)\in O_{\beta_{s+1}}\}.
$$

由 $C_s$ 的连续性及 $O_{\beta_{s+1}}$ 的开放性，$V_{s+1}$ 仍是包含 $x$ 的开集，而

$$
C_{s+1}=F_{\beta_{s+1}}\circ C_s
$$

在其上良定义且连续可微。如此递推，得到 $C_r=C_p$ 在开邻域 $V_r$ 上良定义且连续可微。

再计算导数。第一步有 $DC_1(x)=A_{p,1}(x)$。对 $2\le s\le r$，由链式法则，

$$
\begin{aligned}
DC_s(x)
&=DF_{\beta_s}\bigl(C_{s-1}(x)\bigr)\,DC_{s-1}(x)\\
&=A_{p,s}(x)\,DC_{s-1}(x).
\end{aligned}
$$

逐次代入即得

$$
DC_p(x)=A_{p,r}(x)\cdots A_{p,1}(x).
$$

最后，设 $W$ 是 $x$ 的开邻域且 $W\subseteq U_p$。对每个 $y\in W$，网络均沿路径 $p$ 求值，各步输入均属于相应节点的定义域。在这些输入处，扩展映射 $F_{\beta_s}$ 与局域算子 $f_{\beta_s}$ 一致，因此由 [命题 5.7](<05-operator-networks.md#user-content-oet-56edb9917107efcd>) 的路径分解，

$$
\phi_{\mathcal N}(y)=c_p(y)=C_p(y).
$$

故网络外延算子与 $C_p$ 在 $x$ 的开邻域 $W\cap V_r$ 上相等，从而

$$
D\bigl(\phi_{\mathcal N}\big|_W\bigr)(x)=DC_p(x).
$$

$\square$

这里的 $DC_p(x)$ 按选定的节点扩展 $F_\beta$ 计算。本命题关于外延算子导数的结论仅在存在开邻域 $W\subseteq U_p$ 时适用；不满足该条件时，本命题不作连续性或可微性结论。不同扩展的比较见 [习题 C.2](<#mb-exercise-oet-84ef8daaa0e28176>)。

为考察路径导数在不同正交块之间的作用，固定正交直和分解

$$
\mathbb R^n
=
V_1\perp\cdots\perp V_h,
$$

记 $P_a$ 为到 $V_a$ 的正交投影，并令 $H=\{1,\ldots,h\}$。固定路径 $p$ 与 $x\in U_p$。一条块通路要求每一步从输入块到输出块的线性映射均非零；下面给出它与路径复合导数的关系。


<a id="oet-f8dabd5aec160cd3"></a>

**推论 C.2（非零路径块导数的通路必要条件）**：对任意 $a_0,a_r\in H$，若 $P_{a_r}\circ DC_p(x)\circ P_{a_0}\ne0$，则存在中间块指标 $a_1,\ldots,a_{r-1}\in H$，使

$$
P_{a_s}\circ A_{p,s}(x)\circ P_{a_{s-1}}\ne0
\qquad(1\le s\le r).
$$

反向一般不成立。

**证明**：由 [命题 C.1](<#user-content-oet-6de8b6950c13065a>)，在相邻 Jacobi 因子之间插入恒等分解

$$
\operatorname{id}_{\mathbb R^n}
=
\sum_{a\in H}P_a,
$$

并利用 $P_a^2=P_a$ 展开有限乘积，得到

$$
\begin{aligned}
&P_{a_r}\circ DC_p(x)\circ P_{a_0}\\
&\quad=\sum_{a_1,\ldots,a_{r-1}\in H}
\bigl(P_{a_r}\circ A_{p,r}(x)\circ P_{a_{r-1}}\bigr)
\circ\cdots\circ
\bigl(P_{a_1}\circ A_{p,1}(x)\circ P_{a_0}\bigr).
\end{aligned}
$$

当 $r=1$ 时，没有中间块指标，右侧只含一个求和项。左侧非零，故右侧至少有一个非零求和项；该项的各个块因子都必须非零，因而得到所需的块通路。

为说明反向不成立，在 $\mathbb R^2\cup\{\bot\}$ 上取两个串联节点，局域算子在 $\mathbb R^2$ 上依次采用 [命题 B.15](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-8b08064a80bd8c55>) 中的两步线性映射，在 $\bot$ 处取 $\bot$。第一节点的入口片与通向第二节点的边域均为 $\mathbb R^2$，第二节点无出边。每个输入均沿这两个节点求值后终止，故得到一条实际可达路径。

取 $H=\{1,2\}$ 及两个坐标轴组成的一维正交块分解。由所引命题中的矩阵计算，输入块 $1$ 到输出块 $1$ 之间有两条非零块通路，相应矩阵条目的两个通道乘积分别为 $1$ 与 $-1$，而复合导数的对应块为零。因此块通路存在不排除不同通路项相消。$\square$

上面计算了固定输入处的导数及其块展开。下面在各节点发生的实际输入集上取得统一距离上界，再沿路径复合。

对固定路径 $p=(\beta_1,\ldots,\beta_r)$，沿用 [命题 5.19](<05-operator-networks.md#user-content-oet-3d5365e74a8359df>) 中第 $s$ 个节点发生的实际输入域记号。在本节的轨迹表示下，

$$
D_{p,s}^{\mathrm{in}}
=
\{x_{p,s-1}(x):x\in U_p\}
\subseteq U_{\beta_s}.
$$


<a id="oet-282a390854b22758"></a>

**推论 C.3（节点发生域上的导数证书）**：设对每个 $1\le s\le r$，存在非空凸集

$$
D_{p,s}^{\mathrm{in}}
\subseteq Q_{p,s}
\subseteq O_{\beta_s},
$$

并且矩阵

$$
L_{p,s;i\to j}
:=
\sup_{z\in Q_{p,s}}
\left|
\frac{\partial(F_{\beta_s})_j}{\partial x_i}(z)
\right|
$$

对所有 $i,j\in I$ 均有限。记 $\mathbf L_{p,s}=(L_{p,s;i\to j})$。则

$$
\mathbf L_{p,r}\cdots\mathbf L_{p,1}
\in
\mathscr L(c_p)\big|_{U_p}.
$$

对上述正交分解，若改定义

$$
L^V_{p,s;a\to b}
:=
\sup_{z\in Q_{p,s}}
\left\|
P_b\circ DF_{\beta_s}(z)\circ P_a
\right\|_{2\to2}
$$

且所有条目有限，则相应块矩阵乘积

$$
\mathbf L^V_{p,r}\cdots\mathbf L^V_{p,1}
$$

是 $c_p$ 在 $U_p$ 上关于正交块规范族的 Lip 证书。

**证明**：在每个非空凸集 $Q_{p,s}$ 上应用 [命题 B.5](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-454cb30cfc37f08c>) 或 [命题 B.9](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-460dce986b592798>)，分别得到扩展映射 $F_{\beta_s}$ 的坐标或正交块 Lip 上界。线段估计在扩展映射的定义域 $O_{\beta_s}$ 内进行，因此允许 $Q_{p,s}$ 超出节点原来的定义域 $U_{\beta_s}$。

将上述估计限制到实际输入集 $D_{p,s}^{\mathrm{in}}$，由 $F_{\beta_s}$ 与 $f_{\beta_s}$ 在该集上一致，得到 $f_{\beta_s}$ 在该发生域上的合法 Lip 证书。由定义，$D_{p,1}^{\mathrm{in}}=U_p$，且 $D_{p,s+1}^{\mathrm{in}}=f_{\beta_s}(D_{p,s}^{\mathrm{in}})$（$1\le s<r$）；路径合法性保证 $U_p\subseteq\operatorname{dom}(c_p)$。因此，以 $U_p$ 为起始域应用 [推论 2.5](<02-operator-bounds.md#user-content-oet-c80171fa685dc795>) 的 (i)，即得所示矩阵乘积。$\square$


<a id="oet-1fc7e6eee4342892"></a>

### C.2 仿射网络

下面转向局域算子具有仿射扩展的网络。仿射复合给出每条路径上的作用公式，路由条件决定公式实际适用的输入域；网络之间的复合还会进一步细分这些域。

称 $Q\subseteq\mathbb R^n$ 为一个**线性单元**，若它可由有限多个仿射等式、严格不等式与非严格不等式的共同解集表示。


<a id="oet-f2b0bcadc14fb5ac"></a>

**命题 C.4（仿射局域算子的路径单元）**：设每个节点局域算子在 $U_\beta$ 上由仿射映射

$$
F_\beta(x)=A_\beta x+b_\beta
$$

给出。进一步假设所有入口输入片 $U_\beta^{\mathrm{in}}$、边域 $D_{\beta\to\gamma}$ 与终止域 $T_\beta$ 都是线性单元。

**(i)** 对路径

$$
p=(\beta_1,\ldots,\beta_r)\in\mathcal P(\mathcal N),
$$

令

$$
C_{p,s}
=
F_{\beta_s}\circ\cdots\circ F_{\beta_1}
\qquad(1\le s\le r).
$$

则路径域具有表达

$$
\begin{aligned}
U_p
&=
U_{\beta_1}^{\mathrm{in}}
\cap
\bigcap_{s=1}^{r-1}
C_{p,s}^{-1}
\bigl(D_{\beta_s\to\beta_{s+1}}\bigr)
\cap
C_{p,r}^{-1}
\bigl(T_{\beta_r}\bigr).
\end{aligned}
$$

因而 $U_p$ 是线性单元，且 $c_p\big|_{U_p}=C_{p,r}\big|_{U_p}$。网络外延算子在 $U$ 上是由有限路径域分划给出的分片仿射映射。

**(ii)** 上述分片仿射表示不保证 $\phi_{\mathcal N}\big|_U$ 在不同路径域的交界处连续。

**证明**：**(i)** 沿路径 $p$ 求值的输入必然满足所示入口、逐步转移和终止条件。反之，若 $x$ 属于右侧交集，则 $x\in U_{\beta_1}^{\mathrm{in}}\subseteq U_{\beta_1}$。每个边域满足 $D_{\beta_s\to\beta_{s+1}}\subseteq U_{\beta_{s+1}}$，故可归纳地确认：每步中间点都在对应节点的定义域内，仿射扩展的值与真实局域算子的值一致，并按指定边继续。最后一个条件保证在 $\beta_r$ 终止。因此它确实沿 $p$ 求值，交式成立。$r=1$ 时，边域条件对应的空交取为 $\mathbb R^n$。

有限多个线性单元取交，只需合并其约束；仿射原像则把各约束与仿射映射复合，仍得到仿射等式或同方向不等式。各 $C_{p,s}$ 都是仿射映射，故所示交式给出线性单元 $U_p$。再由 [§ 5.3](<05-operator-networks.md#user-content-oet-374f884cd4d69e88>) 的有限路径分解，得到外延算子的有限分片仿射表示。

**(ii)** 取 $n=1$、$U=\mathbb R$，使用两个无出边入口节点，其入口片分别为

$$
U_1^{\mathrm{in}}=(-\infty,0),
\qquad
U_2^{\mathrm{in}}=[0,+\infty).
$$

两个节点的定义域均取 $\mathbb R$，局域算子在其中分别为常值仿射映射 $F_1(x)=0$ 与 $F_2(x)=1$，在 $\bot$ 处均取 $\bot$；终止域分别为 $T_1=\{0\}$ 与 $T_2=\{1\}$。这给出求值长度恒为 $1$ 的有限算子网络。所有入口片和终止域均为线性单元，网络外延算子在 $U$ 上满足

$$
\phi_{\mathcal N}(x)
=
\begin{cases}
0,&x<0,\\
1,&x\ge0,
\end{cases}
$$

故在 $0$ 处不连续。$\square$


<a id="oet-292cbcc4dd47c8cc"></a>

**命题 C.5（仿射网络外延的复合封闭性）**：设 $\mathcal N_1,\mathcal N_2$ 的输入域分别为 $U_1,U_2$，且两网均满足 [命题 C.4](<#user-content-oet-f2b0bcadc14fb5ac>) 的仿射与线性单元条件。记各路径上的仿射表达为

$$
F_p(x)=A_px+b_p,
\qquad
G_q(y)=B_qy+d_q.
$$

在复合的有效域

$$
D:=\{x\in U_1:\phi_{\mathcal N_1}(x)\in U_2\}
$$

上，所有非空集合

$$
U_{p,q}:=U_p^{(1)}\cap F_p^{-1}(U_q^{(2)})
$$

构成有限线性单元分划，且

$$
(\phi_{\mathcal N_2}\circ\phi_{\mathcal N_1})(x)
=B_qA_px+B_qb_p+d_q
\qquad(x\in U_{p,q}).
$$

存在同样满足上述仿射与线性单元条件的有限网络 $\mathcal M$，其输入域为 $D$，且 $\phi_{\mathcal M}=\phi_{\mathcal N_2}\circ\phi_{\mathcal N_1}$；$D=\emptyset$ 时取空网络。

**证明**：对 $x\in D$，第一网有唯一实际路径 $p$，而 $F_p(x)=\phi_{\mathcal N_1}(x)\in U_2$ 在第二网中又有唯一实际路径 $q$。因此 $x$ 恰属于一个 $U_{p,q}$。反之，属于某个 $U_{p,q}$ 的点满足复合有效域条件；两网路径集有限，故得到所述有限分划。

由 [命题 C.4](<#user-content-oet-f2b0bcadc14fb5ac>)，各 $U_p^{(1)}$ 与 $U_q^{(2)}$ 为线性单元。仿射原像及有限交保持线性单元，所以 $U_{p,q}$ 也是线性单元。在该域内依次代入两条路径的仿射式，即得复合公式。

若 $D\ne\emptyset$，对每个非空 $U_{p,q}$ 设置一个无出边入口节点，其入口片为 $U_{p,q}$，局域算子在 $\mathbb R^n$ 上取仿射映射 $G_q\circ F_p$，在 $\bot$ 处取 $\bot$。该节点的终止域是 $(G_q\circ F_p)(\mathbb R^n)$，为一个仿射子空间；选取其方向空间正交补的一组基，可将它写成有限个仿射等式的共同解集，故也是线性单元。

各入口片非空且分划 $D$，每次求值在所选入口节点一次终止，因此满足入口唯一、统一有限终止及无冗余节点条件，出边条件为空。所得网络 $\mathcal M$ 在 $D$ 上给出上述复合，在域外取 $\bot$，所以外延相等。若 $D=\emptyset$，复合处处为 $\bot$，由空网络实现。$\square$

该构造给出复合的一种网络表示。它按路径对分别设置节点，不保留原网络的节点共享；结论不指定网络对象之间的典范复合运算。

网络中的实际发生域还可能落在低维仿射子空间内。以下沿用 [引理 B.13](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-5327d971cf04c4ca>) 的方向空间 $W_S=\operatorname{span}(S-S)$，在实际域上读取矩阵作用。


<a id="oet-e4b8f2d657424bba"></a>

**命题 C.6（仿射发生域与路径中的变化方向）**：设 $\mathcal N$ 的节点仿射表达为 $F_\beta(x)=A_\beta x+b_\beta$。

**(i) 发生域与阈值。** 若入口片与边域均为线性单元，则每个可达前缀 $q=(\beta_1,\ldots,\beta_s)$ 的实际发生域 $D_q^{\mathrm{in}}$ 非空且凸。采用坐标规范族及任意有限正阈值 $\tau_\sigma,\tau_{\mathrm N}$ 时，

$$
\operatorname{Type}_q(i,j)
=\left(
\mathbf1_{\{\sigma_i(D_q^{\mathrm{in}})<\tau_\sigma\}},
\mathbf1_{\{(A_{\beta_s})_{j\bullet}|_{W_{D_q^{\mathrm{in}}}}=0\}}
\right).
$$

第二项等于 $1$ 当且仅当末节点的第 $j$ 个输出坐标在该发生域上为常值。

**(ii) 固定路径中的方向。** 固定完整可达路径 $p=(\beta_1,\ldots,\beta_r)\in\mathcal P(\mathcal N)$，记 $C_{p,s}=F_{\beta_s}\circ\cdots\circ F_{\beta_1}$。令 $D_0=U_p$，$D_s=C_{p,s}(U_p)$（$1\le s\le r$），并记 $W_s=W_{D_s}$。则

$$
W_s=A_{\beta_s}(W_{s-1}),
\qquad
\dim W_s\le\dim W_{s-1}
\quad(1\le s\le r).
$$

这一分项不要求入口片、边域或终止域是线性单元。

**证明**：**(i)** 令 $C_{q,t}=F_{\beta_t}\circ\cdots\circ F_{\beta_1}$。沿用可达前缀的初始域 $U[q\ast]$，有

$$
U[q\ast]
=U_{\beta_1}^{\mathrm{in}}
\cap\bigcap_{t=1}^{s-1}
C_{q,t}^{-1}(D_{\beta_t\to\beta_{t+1}}).
$$

沿该前缀求值的输入满足右侧条件。反之，右侧条件逐步保证节点作用有定义并沿指定边继续；网络从每个入口输入出发均唯一有限终止，所以该前缀必能延续为一条完整实际路径。不需要另加末节点的终止条件。$s=1$ 时，空交取为 $\mathbb R^n$。

右侧是线性单元，因而凸。$q$ 可达保证它非空；$D_q^{\mathrm{in}}$ 在 $s=1$ 时等于该集合，在 $s>1$ 时是它在 $C_{q,s-1}$ 下的仿射像，所以也非空且凸。在这个域上对末节点 $f_q=f_{\beta_s}$ 应用 [命题 B.14](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-055e3702cf9c3930>) 的 (ii)，得到

$$
\underline{r}^{\mathrm N}_q(i,j)=
\begin{cases}
+\infty,&(A_{\beta_s})_{j\bullet}|_{W_{D_q^{\mathrm{in}}}}=0,\\
0,&\text{否则}.
\end{cases}
$$

因 $0<\tau_{\mathrm N}<+\infty$，代入 [§ 5.5](<05-operator-networks.md#user-content-oet-4b1389b158d2780e>) 的阈值定义即得分类式；常值解释由 [引理 B.13](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-5327d971cf04c4ca>) 给出。

**(ii)** 此处始终使用同一完整路径域 $U_p$。由 $D_s=F_{\beta_s}(D_{s-1})$ 及 [引理 B.13](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-5327d971cf04c4ca>)，得到 $W_s=A_{\beta_s}(W_{s-1})$。线性映射的像空间维数不超过定义域维数，故得到逐步不增式。$\square$

方向空间的维数与常值坐标的数量不同。例如两步作用 $F(s,t)=(s,0)$、$G(u,v)=(u,u)$ 将 $\mathbb R^2$ 先映到横轴，再映到对角线。两次像的方向空间均为一维，而第二个输出坐标由常值变为可变。这是 [命题 3.3](<03-operator-local-degeneracy.md#user-content-oet-2c5dc85febaac657>) 中常值分量不一定向后保持的具体情形。类似地，[命题 C.4](<#user-content-oet-f2b0bcadc14fb5ac>) 的阶跃例中，各路径分别常值，整个网络却不为常值；路径内的结论仍须限定在对应路径域上。

输出覆盖估计只需节点具有仿射扩展，不要求入口片、边域或终止域是线性单元。对路径 $p=(\beta_1,\ldots,\beta_r)$，写

$$
c_p(x)=A_px+b_p\quad(x\in U_p),
\qquad
A_p=A_{\beta_r}\cdots A_{\beta_1},
$$

并令

$$
r_p=\operatorname{rank}(A_p|_{W_{U_p}})
=\dim W_{c_p(U_p)}.
$$

由 [引理 B.13](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-5327d971cf04c4ca>)，$r_p$ 由实际受限映射 $c_p|_{U_p}$ 决定，且不超过 $\operatorname{rank}(A_p)$。以下仍使用所选全空间仿射扩展的算子范数，因此维数指数不依赖扩展，整个上界的数值则仍可能依赖这一选择。


<a id="oet-c9e4b6fb4f7e4e59"></a>

**推论 C.7（路径限制秩给出的网络输出覆盖上界）**：设 $\varepsilon>0$。若对每个 $p\in\mathcal P(\mathcal N)$，存在 $x_p\in U_p$ 与有限 $R_p\ge0$，使

$$
U_p
\subseteq
\overline B_2(x_p,R_p),
$$

则

$$
\mathcal N_{\mathrm{Euc}}
\bigl(\varepsilon,\phi_{\mathcal N}(U)\bigr)
\le
\sum_{p\in\mathcal P(\mathcal N)}
\left(
1+
\frac{2\|A_p\|_{2\to2}R_p}{\varepsilon}
\right)^{r_p}.
$$

当 $r_p=0$ 时，对应项等于 $1$。

**证明**：固定路径 $p$。对任意 $x\in U_p$，

$$
c_p(x)-c_p(x_p)
=
A_p(x-x_p),
$$

结合 $\|x-x_p\|_2\le R_p$，得到

$$
c_p(U_p)
\subseteq
\bigl(c_p(x_p)+A_p(W_{U_p})\bigr)
\cap
\overline B_2\bigl(c_p(x_p),\|A_p\|_{2\to2}R_p\bigr).
$$

这里 $x-x_p\in W_{U_p}$，而 $A_p(W_{U_p})$ 的维数为 $r_p$；半径 $\|A_p\|_{2\to2}R_p$ 有限非负，且 $x_p\in U_p$ 保证 $c_p(U_p)$ 非空。对这一实际路径像集应用 [命题 B.4](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-a57e9e873735ed63>) 的 (i)，得到

$$
\mathcal N_{\mathrm{Euc}}
(\varepsilon,c_p(U_p))
\le
\left(
1+
\frac{2\|A_p\|_{2\to2}R_p}{\varepsilon}
\right)^{r_p}.
$$

最后使用 [命题 5.13](<05-operator-networks.md#user-content-oet-13da76fc7723fdef>) 的路径输出有限并覆盖上界并对 $p$ 求和。$r_p=0$ 时 $c_p(U_p)$ 为单点，对应覆盖数为 $1$。$\square$

该公式的右侧同时使用路径数、各路径实际输出的仿射维数、路径域半径与线性放大。若只使用环境矩阵秩，则由 $r_p\le\operatorname{rank}(A_p)$ 和底数不小于 $1$，仍可得到较宽的覆盖上界。

有限维表示把网络作用分成两层：路径内部的复合，以及路径域之间的分划。可微条件下，前者给出导数与距离证书，后者决定这些公式适用于哪些输入。仿射条件下，路径单元还可用于构造网络复合，实际域的方向空间则把常值分量、零化判据和输出覆盖中的维数联系起来。

使用这些结果时，须保留其实际评估域。固定路径的估计不自动控制跨路径点对；扩展映射的导数，以及仿射扩展线性部分的算子范数，可能随扩展选择改变，实际方向空间上的仿射限制则由域内作用确定。


<a id="oet-65c92929f51de5ac"></a>

### C.3 习题


<div data-mb-exercise="oet-b3f71b0e8b87fbf0">

**习题 C.1（仿射路由与路径秩）**：在 $\mathcal X=\mathbb R^2\cup\{\bot\}$ 上取三个节点 $\alpha,\beta,\gamma$，局域算子在 $\mathbb R^2$ 上分别为

$$
f_\alpha(s,t)=(s,t),\qquad f_\beta(s,t)=(s,0),\qquad f_\gamma(s,t)=(0,t),
$$

并在 $\bot$ 处取 $\bot$。唯一入口片为 $U_\alpha^{\mathrm{in}}=U=[-1,1]^2$。仅设置两条边 $\alpha\to\beta$ 与 $\alpha\to\gamma$，转移域分别为 $\{(s,t):s<0\}$ 与 $\{(s,t):s\ge0\}$；$\beta,\gamma$ 均无出边。以下选用所列全空间线性映射作为节点扩展，并采用欧氏距离。

**(i)** 验证这是一组有限算子网络数据，求全部可达路径、路径域、路径复合及网络输出集合。

**(ii)** 求两条路径线性部分的秩和欧氏算子范数。分别取路径域中心 $(-1/2,0)$ 与 $(1/2,0)$，验证半径 $R=\sqrt5/2$ 可用，并由 [推论 C.7](<#user-content-oet-c9e4b6fb4f7e4e59>) 证明

$$
\mathcal N_{\mathrm{Euc}}(\varepsilon,\phi_{\mathcal N}(U))
\le 2\left(1+\frac{\sqrt5}{\varepsilon}\right)
\qquad(\varepsilon>0).
$$

说明这里的维数指数为何是 $1$，而不是环境维数 $2$。

</div>



<div data-mb-exercise="oet-84ef8daaa0e28176">

**习题 C.2（受限映射的仿射扩展）**：取 $U=[-1,1]\times\{0\}\subseteq\mathbb R^2$，定义

$$
F(s,t)=(s,0),\qquad G(s,t)=(s,t).
$$

将 $F|_U$ 在域外补为 $\bot$，作为单节点网络的局域算子；入口片为 $U$，无出边。

**(i)** 验证 $F|_U=G|_U$，分别求 $DF$、$DG$ 及其秩。

**(ii)** 求 $W_U$，比较 $DF|_{W_U}$ 与 $DG|_{W_U}$ 及其秩。分别选用 $F$ 与 $G$ 作为节点扩展，说明 [推论 C.7](<#user-content-oet-c9e4b6fb4f7e4e59>) 中的维数指数为何相同，而采用整个矩阵秩会给出怎样的差别。

</div>



<div data-mb-exercise="oet-64877d77e522a25b">

**习题 C.3（块通路的范数界与复合）**：

**(i)** 沿用 [§ C.1](<#user-content-oet-ac1e85729aad39ca>) 的可微扩展与正交分解。对任意可达路径 $p$、$x\in U_p$ 与端点块 $a_0,a_r\in H$，利用 [推论 C.2](<#user-content-oet-f8dabd5aec160cd3>) 证明中的块展开式，证明

$$
\|P_{a_r}\circ DC_p(x)\circ P_{a_0}\|_{2\to2}
\le
\sum_{a_1,\ldots,a_{r-1}\in H}
\prod_{s=1}^r
\|P_{a_s}\circ A_{p,s}(x)\circ P_{a_{s-1}}\|_{2\to2}.
$$

当 $r=1$ 时，右侧没有中间块指标，求和只含一项。

**(ii)** 在 $\mathbb R^2$ 上取单块正交分解 $V_1=\mathbb R^2$，并令

$$
A=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
B=\begin{pmatrix}0&0\\0&1\end{pmatrix}.
$$

对依次作用的线性映射 $x\mapsto Ax$、$x\mapsto Bx$，判断两步各自的块映射是否非零，计算复合映射，并用 $\operatorname{im}(A)$ 与 $\ker(B)$ 的关系解释计算结果。说明这个例子为何不涉及不同块通路之间的相消。

</div>



<div data-mb-exercise="oet-b3af1b7e2f078cb4">

**习题 C.4（低维发生域上的常值与阈值）**：设网络采用 $\mathbb R^2$ 的坐标规范族，某个可达前缀 $q$ 的实际发生域与末节点作用分别为

$$
D_q^{\mathrm{in}}=\{(t,t):-1\le t\le1\},
\qquad
f_q(s,t)=(s-t,s+t).
$$

这里 $f_q$ 表示该次发生的末节点作用，不是整个前缀的复合。

**(i)** 求 $W_{D_q^{\mathrm{in}}}$ 与该次发生的常值分量。说明为什么节点矩阵的一行非零，仍可能对应常值输出分量。

**(ii)** 采用坐标直径尺度并取 $\tau_\sigma=\tau_{\mathrm N}=1$，计算所有通道的 $\underline{r}^{\mathrm N}_q(i,j)$ 与 $\operatorname{Type}_q(i,j)$。说明这里应使用凸域上的受限判据，而不能直接采用开域中的整行判据。

</div>
