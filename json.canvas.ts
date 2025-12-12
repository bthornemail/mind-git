declare enum CanvasColor {
    RED = 1,
    ORANGE = 2,
    YELLOW = 3,
    GREEN = 4,
    CYAN = 5,
    PURPLE = 6
}

type EdgeSide = "top" | "right" | "bottom" | "left";
type EdgeEnd = "none" | "arrow";
interface Edge {
    id: string;
    fromNode: string;
    fromSide?: EdgeSide;
    fromEnd?: EdgeEnd;
    toNode: string;
    toSide?: EdgeSide;
    toEnd?: EdgeEnd;
    color?: CanvasColor;
    label?: string;
}

interface GenericNode {
    id: string;
    x: number;
    y: number;
    width: number;
    height: number;
    color?: CanvasColor;
}
type Node = {
    type: "text" | "file" | "link" | "group";
    file?: string;
    label?: string;
} & GenericNode;
interface TextNode extends GenericNode {
    type: "text";
    text: string;
}
interface LinkNode extends GenericNode {
    type: "link";
    url: string;
}
interface FileNode extends GenericNode {
    type: "file";
    subpath?: string; // (optional, string) is a subpath that may link to a heading or a block. Always starts with a #
}
type GroupNodeBackgroundStyle = "cover" | "ratio" | "repeat";
interface GroupNode {
    type: "group";
    label?: string;
    background?: string;
    backgroundStyle?: GroupNodeBackgroundStyle;
}
interface JSONCanvas {
    nodes: Partial<Node>[];
    edges: Partial<Edge>[];
}
export { type JSONCanvas, CanvasColor, type Edge, type EdgeEnd, type EdgeSide, type GenericNode, type GroupNode, type Node,type LinkNode, type TextNode };