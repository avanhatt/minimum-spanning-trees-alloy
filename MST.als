open util/integer
open lib/graph
open lib/basicproperties

pred isSpanningTree(g, tree : Graph) {
    g.vertices = tree.vertices
    tree.edges in g.edges
    undirectedAcyclic[tree]
    connected[tree]
}

pred isMST(g, tree : Graph) {
    isSpanningTree[g, tree]
    no tree2 : Graph {
        isSpanningTree[g, tree2]
        gt[sum edge : tree.edges | weight, 
           sum edge : tree2.edges | weight]
	}
}

run isSpanningTree
