extern
fun{}
slseg_node_set_next {l1,l2,l3:addr} (!slseg_node (l1) @ l2 >> slseg_node (l3) @ l2 | ptr l2, ptr l3): void
extern
fun{}
slseg_node_get_next {l1,l2:addr} (!slseg_node (l1) @ l2 | ptr l2): ptr l1
extern
fun{}
slseg_node_free {l1,l2:addr} (slseg_node_mfree_v (l2), slseg_node (l1) @ l2 | ptr l2): void
