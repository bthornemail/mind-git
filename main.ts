import { JSONCanvas } from '@trbn/jsoncanvas';
import { JSONCanvas as CanvasJSON, CanvasColor, Edge, EdgeEnd, EdgeSide, GenericNode, GroupNode, LinkNode, TextNode } from './json.canvas';

const parseCanvas = (canvas: JSONCanvas) => JSON.parse(canvas.toString());

const canvas: CanvasJSON = parseCanvas(new JSONCanvas());

const prediction: CanvasJSON = {
    "nodes": [
        { "id": "9e905a6724ee0e6a", "x": -223, "y": -20, "width": 940, "height": 592, "type": "group", "label": "Untitled group" },
        { "id": "vertice-6", "type": "file", "file": "Esp32-C6.md", "x": 2400, "y": 235, "width": 180, "height": 235 },
        { "id": "point-7", "type": "file", "file": "Port.md", "x": 134, "y": 649, "width": 186, "height": 114 },
        { "id": "line-8", "type": "file", "file": "Protocol.md", "x": 134, "y": 878, "width": 186, "height": 114 },
        { "id": "plane-9", "type": "file", "file": "Program.md", "x": 134, "y": 1120, "width": 186, "height": 114 },
        { "id": "affine-10", "type": "file", "file": "Procedure.md", "x": 134, "y": 1360, "width": 186, "height": 114 },
        { "id": "projection-11", "type": "file", "file": "Presentation.md", "x": 134, "y": 1600, "width": 219, "height": 83 },
        { "id": "centroid-0", "type": "file", "file": "Esp32-S3.md", "x": 97, "y": 387, "width": 294, "height": 165 },
        { "id": "vertice-3", "type": "file", "file": "Esp32-C6.md", "x": 157, "y": 0, "width": 180, "height": 235 },
        { "id": "vertice-4", "type": "file", "file": "Esp32-C6.md", "x": 337, "y": 0, "width": 180, "height": 235 },
        { "id": "vertice-5", "type": "file", "file": "Esp32-C6.md", "x": 517, "y": 0, "width": 180, "height": 235 },
        { "id": "vertice-1", "type": "file", "file": "Esp32-C6.md", "x": -203, "y": 0, "width": 180, "height": 235 },
        { "id": "vertice-2", "type": "file", "file": "Esp32-C6.md", "x": -23, "y": 0, "width": 180, "height": 235 },
        { "id": "d1a6a95ab19d2fe1", "x": 47, "y": -560, "width": 400, "height": 400, "type": "file", "file": "Person.md" },
        { "id": "peer-12", "type": "file", "file": "Peer.md", "x": 118, "y": 1760, "width": 219, "height": 83 }
    ],
    "edges": []
};
function translate() {
    // Adds an connection between node1 and node2
    canvas.addEdge({
        id: 'edge1',
        fromNode: 'node1',
        toNode: 'node2',
        label: 'Edge 1',
    });
    return canvas.toString();
};
function transform() {
    // Adds a text node to the canvas
    canvas.addNode({
        id: 'node1',
        type: 'text',
        text: 'Hello, World!',
        x: 100,
        y: 100,
        width: 100,
        height: 100,
    });

    // Adds another text node to the canvas
    canvas.addNode({
        id: 'node2',
        type: 'text',
        text: 'Hello, World 2!',
        x: 200,
        y: 200,
        radius: 50,
    });
    return canvas.toString();
};
async function getGeometry(value: CanvasJSON, index: number, array: CanvasJSON[]): Promise<GroupNode> {
    let group: GroupNode = {
        type: 'group'
    };
    return group;
};
async function factor(polynomial: CanvasJSON[] = [prediction]) {
    const cartesianPlane = new JSONCanvas();
    const geometry = polynomial.map(getGeometry);
    for (let i = 0; i <= 20; i++) {
        console.log("N equals", i);
    }
    // Removes node2 and all connections to it
    //    canvas.removeNode('node2');

    console.log("Cartesian Coordinates are:\n", cartesianPlane);
    return parseCanvas(cartesianPlane);
};
(async () => {
    const factorial = await factor()

    console.log("Does code equal result", factorial === prediction);

})()