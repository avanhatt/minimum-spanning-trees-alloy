open util/integer
open lib/graph
open lib/basicProperties

pred isSpanningTree(g, tree : Graph) {
    g.vertices = tree.vertices
    tree.edges in g.edges
    undirectedAcyclic[tree]
	connected[tree]
}

pred isMST(g, tree : Graph) {
    isSpanningTree[g, tree]
    no tree2 : Graph | {
        isSpanningTree[g, tree2]
        gt[sum edge : tree.edges | edge.weight, sum edge : tree2.edges | edge.weight]
    }
}

pred existsMST {
    one graph: Graph | some tree : Graph {
		graph.vertices = Vertex
		complete[graph]
        isMST[graph, tree]
	}
        
}

run isMST for 3 Vertex, 2 Graph, 3 Edge, 1 Univ
