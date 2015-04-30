open util/integer
open lib/graphInheritance
open lib/basicProperties

pred isSpanningTree(g, tree : UGraph) {
	not (g = tree)
    g.vertices = tree.vertices
    tree.edges in g.edges
    undirectedAcyclic[tree]
    connected[tree]
}

pred isInterestingSpanningTree(g, tree : UGraph) {
	isSpanningTree[g, tree]
	not undirectedAcyclic[g]
	all disj g1, g2: UGraph |
		g1.edges != g2.edges
	all edge : Edge |
		gt[edge.weight, 0]
	all disj e1, e2 : Edge |
		e1.weight != e2.weight
}

pred isMST(g, tree : UGraph) {
    isInterestingSpanningTree[g, tree]
    no tree2 : UGraph {
        isInterestingSpanningTree[g, tree2]
        gt[(sum edge : tree.edges | edge.weight), 
           (sum edge : tree2.edges | edge.weight)]
	}
}

run isMST for exactly 3 Vertex, exactly 8 Graph, 3 Edge, 1 Univ
