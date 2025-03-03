from pyslang import Compilation, SyntaxTree, Expression, ExpressionKind, DiagnosticEngine
import networkx as nx
import graphviz
from pathlib import Path


class ExprVisitor:
    def __init__(self):
        self._edges = {}
        self._expr_id = {}
        self._id_syntax = {}
        self._expr_text = {}
        self._next_id = 0

    @property
    def graphs(self):
        edges = list(self._edges.keys())
        g = nx.DiGraph(edges)

        graphs = []
        for comp in nx.connected_components(nx.to_undirected(g)):
            g_comp = nx.subgraph(g, comp)
            base_node = next(nx.lexicographical_topological_sort(g_comp))

            dot_g = graphviz.Digraph()

            for n_id in g_comp.nodes:
                dot_g.node(n_id, self._expr_text[n_id])

            for (p_id, c_id) in g_comp.edges:
                dot_g.edge(p_id, c_id, self._edges[(p_id, c_id)])

            dot_g.node("legend", self._id_syntax[base_node], shape="rect")
            graphs.append(dot_g)

        return graphs

    def visit(self, node):
        if isinstance(node, Expression):
            node_id = self._get_expr_id(node)
            node_children = self._node_children(node)

            for child_id, edge_label in node_children:
                self._edges[(node_id, child_id)] = edge_label

    @staticmethod
    def _node_text(node):
        match node.kind:
            case ExpressionKind.NamedValue:
                return f"{node.symbol.name}: {node.type}"
            case ExpressionKind.IntegerLiteral:
                return f"{node.value}: {node.type}"
            case ExpressionKind.StringLiteral:
                return f"'{node.value}': {node.type}"
            case ExpressionKind.Conversion:
                return f"{node.operand.type} -> {node.type}"
            case ExpressionKind.BinaryOp:
                return f"{node.kind.name}({node.op.name})\\n{node.type}"
            case ExpressionKind.UnaryOp:
                return f"{node.kind.name}({node.op.name})\\n{node.type}"
            case ExpressionKind.Call:
                return f"{node.kind.name}({node.subroutineName})\\n{node.type}"
            case ExpressionKind.TaggedUnion:
                return f"{node.kind.name}({node.member.name})\\n{node.type}"
            case ExpressionKind.MemberAccess:
                return f"{node.kind.name}({node.member.name})\\n{node.type}"
            case _:
                return f"{node.kind.name}\\n{node.type}"

    def _node_children(self, node: Expression):
        children = []
        match node.kind:
            case ExpressionKind.NamedValue:
                pass
            case ExpressionKind.IntegerLiteral:
                pass
            case ExpressionKind.StringLiteral:
                pass
            case ExpressionKind.LValueReference:
                pass
            case ExpressionKind.Conversion:
                children = [(node.operand, "arg")]
            case ExpressionKind.BinaryOp:
                children = [(node.left, "lhs"), (node.right, "rhs")]
            case ExpressionKind.UnaryOp:
                children = [(node.operand, "operand")]
            case ExpressionKind.Call:
                children = [(op, "arg") for op in node.arguments]
            case ExpressionKind.RangeSelect:
                children = [(node.left, "left"), (node.right, "right"), (node.value, "value")]
            case ExpressionKind.Assignment:
                children = [(node.left, "lhs"), (node.right, "rhs")]
            case ExpressionKind.Concatenation:
                children = [(op, "operand") for op in node.operands]
            case ExpressionKind.Replication:
                children = [(node.count, "count"), (node.concat, "concat")]
            case ExpressionKind.MinTypMax:
                children = [(node.min, "min"), (node.typ, "typ"), (node.max, "max")]
            case ExpressionKind.Inside:
                children = [(node.left, "left")] + [(elm, "range") for elm in node.rangeList]
            case ExpressionKind.Streaming:
                children = [(elm.operand, "stream") for elm in node.streams]
            case ExpressionKind.NewArray:
                children = [(node.sizeExpr, "size")]
            case ExpressionKind.ElementSelect:
                children = [(node.value, "value"), (node.selector, "selector")]
            case ExpressionKind.TaggedUnion:
                children = [(node.valueExpr, "value")] if node.valueExpr is not None else []
            case ExpressionKind.MemberAccess:
                children = [(node.value, "value")]
            case ExpressionKind.NewClass:
                children = [(node.constructorCall, "constructor")]
            case ExpressionKind.ConditionalOp:
                children = ([(node.left, "true"), (node.right, "false")] +
                            [(elm.expr, "condition") for elm in node.conditions])
            case e:
                raise NotImplementedError(e)

        def get_id(x):
            expr, lbl = x
            return self._get_expr_id(expr), lbl

        return map(get_id, children)

    def _get_expr_id(self, node):
        if node not in self._expr_id:
            n_id = str(self._next_id)
            self._expr_id[node] = n_id
            self._id_syntax[n_id] = str(node.syntax).strip()
            self._expr_text[n_id] = self._node_text(node)
            self._next_id += 1

        return self._expr_id[node]


def main(file: Path, out_dir: Path):
    tree = SyntaxTree.fromFile(str(file))

    c = Compilation()
    c.addSyntaxTree(tree)

    print(DiagnosticEngine.reportAll(c.sourceManager, c.getAllDiagnostics()))

    ev = ExprVisitor()
    c.getRoot().visit(ev.visit)

    out_dir.mkdir(exist_ok=True)

    for g_id, g in enumerate(ev.graphs):
        g.render(out_dir / f"graph-{file.stem}-{g_id}.dot", view=True)


main(Path("input.v"), Path("out/"))
