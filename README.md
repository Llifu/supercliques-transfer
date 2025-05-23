## The SC-Trans and ICP algorithm

This is the repository of the " An Improved Clique-picking Algorithm for Counting Markov Equivalent DAGs via Super Cliques Transfer" paper. Our experiments are based on https://github.com/mwien/CliquePicking.

### Experimental details
The instances are undirected connected and chordal graphs generated by minimal triangulation method. The folder `instances` contains two subfolders `Varying numbers of graph vertices` and `Varying graph densities`, which are of the same name of the subsections of section 7 in our paper. The instances in the subfolders are named as `<number> <density> <x>`, where `x = 1,...,10`(Due to transmission limitations, only some instances are shown). 

### References
Wienöbst, M., Bannach, M., & Liśkiewicz, M. (2023). Polynomial-Time Algorithms for Counting and Sampling Markov Equivalent DAGs with Applications. Journal of Machine Learning Research, 24(213), 1-45. https://www.jmlr.org/papers/volume24/22-0495/22-0495.pdf
