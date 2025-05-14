using LightGraphs
using LinkedLists
using Combinatorics
using Random

"""
    readgraph(file = stdin, undirected = false)

Read a graph from the standard input or a given file and return a directed simple graph.
In case undirected graphs are read (as in the toy examples we give
here), the argument undirected=true may be passed. Then, each edge can be given only once.
"""
function readgraph(file = stdin, undirected = false)
    if file != stdin
        file = open(file, "r")
    end
    (n, m) = parse.(Int, split(readline(file)))
    readline(file)
    G = SimpleDiGraph(n)
    for i = 1:m
        (a, b) = parse.(Int, split(readline(file)))
        add_edge!(G, a, b)
        undirected && add_edge!(G, b, a)
    end
    return G
end


"""
    ischordal(g)

Return true if the given graph is chordal
"""
function ischordal(G)
    mcsorder, invmcsorder, _ = mcs(G, Set())
    
    n = length(mcsorder)
    
    f = zeros(Int, n)
    index = zeros(Int, n)
    for i=n:-1:1
        w = mcsorder[i]
        f[w] = w
        index[w] = i
        for v in neighbors(G, w)
            if invmcsorder[v] > i
                index[v] = i
                if f[v] == v
                    f[v] = w
                end
            end
        end
        for v in neighbors(G, w)
            if invmcsorder[v] > i
                if index[f[v]] > i
                    return false
                end
            end
        end
    end
    return true
end

"""
    vispush!(l::LinkedList, pointers, x, vis)
"""
@inline function vispush!(l::LinkedList, pointers, x, vis)
    if vis
        pointers[x] = push!(l,x)
    else
        pointers[x] = pushfirst!(l,x)
    end
end

"""
    phi(cliquesize, i, fp, fmemo, pmemo)
Recursively compute the function phi. Initial call is phi(cliquesize, 1, fp, fmemo, pmemo). 
If not used before, fmemo and pmemo should be zero vectors of appropriate size. 
"""
function phi(cliquesize, i, fp, fmemo, pmemo)
    pmemo[i] != 0 && return pmemo[i]
    sum = fac(cliquesize-fp[i], fmemo)
    for j = (i+1):length(fp)
        sum -= fac(fp[j]-fp[i], fmemo) * phi(cliquesize, j, fp, fmemo, pmemo)
    end
    return pmemo[i] = sum
end

"""
    fac(n, fmemo)
Recursively compute the factorial of n using memoization table fmemo.
"""
function fac(n, fmemo)
    fmemo[n] != 0 && return fmemo[n]
    n == 1 && return BigInt(1)
    res = fac(n-1, fmemo) * n
    return fmemo[n] = res
end

"""
    mcs(G, K)
Performs a Maximum Cardinality Search on graph G. 
The elements of K are of prioritised and chosen first. 
Returns the visit order of the vertices, its inverse and the subgraphs C_G(K) (see Def. 1 in [1,2]). 
If K is empty a normal MCS is performed.
The MCS takes the role of the LBFS in [1,2]. Details will be published in future work.
"""
function mcs(G, K)
    n = nv(G)
    copy_K = copy(K)
    
    # data structures for MCS
    sets = [LinkedList{Int}() for i = 1:n+1]
    pointers = Vector(undef,n)
    size = Vector{Int}(undef, n)
    visited = falses(n)
    
    # output data structures
    mcsorder = Vector{Int}(undef, n)
    invmcsorder = Vector{Int}(undef, n)
    subgraphs = Array[]

    # init
    visited[collect(copy_K)] .= true
    for v in vertices(G)
        size[v] = 1
        vispush!(sets[1], pointers, v, visited[v])
    end
    maxcard = 1

    for i = 1:n
        # first, the vertices in K are chosen
        # they are always in the set of maximum cardinality vertices
        if !isempty(copy_K)
            v = pop!(copy_K)
        # afterwards, the algorithm chooses any vertex from maxcard
        else
            v = first(sets[maxcard])
        end
        # v is the ith vertex in the mcsorder
        mcsorder[i] = v
        invmcsorder[v] = i
        size[v] = -1

        # immediately append possible subproblems to the output
        if !visited[v]
            vertexset = Vector{Int}()
            for x in sets[maxcard]
                visited[x] && break
                visited[x] = true
                push!(vertexset, x)
            end
            sg = induced_subgraph(G, vertexset)
            subgraphs = vcat(subgraphs, (map(x -> sg[2][x], connected_components(sg[1]))))
        end

        deleteat!(sets[maxcard], pointers[v])

        # update the neighbors
        for w in inneighbors(G, v)
            if size[w] >= 1
                deleteat!(sets[size[w]], pointers[w])
                size[w] += 1
                vispush!(sets[size[w]], pointers, w, visited[w])
            end
        end
        maxcard += 1
        while maxcard >= 1 && isempty(sets[maxcard])
            maxcard -= 1
        end
    end

    return mcsorder, invmcsorder, subgraphs
end

"""
    cliquetreefrommcs(G, mcsorder, invmcsorder)
"""
function cliquetreefrommcs(G, mcsorder, invmcsorder)
    n = nv(G)
    # data structures for the algorithm
    K = Vector{Set}()
    push!(K, Set())
    s = 1
    edgelist = Vector{Vector}()
    visited = falses(n)
    clique = zeros(Int, n)
    
    # seprators for the algorithm
    Sep = Vector{Set}()
    push!(Sep, Set())
    
    # chile clique
    cclique = [Vector{Int}()]
    
    for i = 1:n
        x = mcsorder[i]
        S = Set{Int}()
        for w in inneighbors(G, x)
            if visited[w]
                push!(S, w)
            end
        end
        
        # if necessary create new maximal clique
        if K[s] != S
            s += 1
            push!(cclique, []) # get child clique
            push!(K, S)
            push!(Sep, copy(S))
            k, _ = findmax(map(x -> invmcsorder[x], collect(S)))
            p = clique[mcsorder[k]]
            push!(edgelist, [p,s])
            push!(cclique[p], s) # get child clique
        end
        
        push!(K[s], x)
        clique[x] = s 
        visited[x] = true;
    end
    K[1] = Set{Int}(K[1])
    Sep[1] = Set{Int}(Sep[1])
    return K, Sep, edgelist, s, cclique
end

"""
    cliquetree(G)
"""
function cliquetree(G)
    mcsorder, invmcsorder, _ = mcs(G, Set())
    K, Sep, edgelist, s, cclique = cliquetreefrommcs(G, mcsorder, invmcsorder)
    return K, Sep, edgelist, s, cclique
end

"""
    SCTrans(K, Sep, edgelist, s)

Generate the set of undirected connected components C_G(K_1), ...,C_G(K_m)
"""
function SCTrans(K, Sep, edgelist, s)
    # Initial the structures of undirected connected components
    Comp = [Set{Int}() for _ in 1:s, _ in 1:s]
    
    if !isempty(edgelist)
        pa = edgelist[1][1]
        Comp[2, pa] = setdiff(K[pa], Sep[2])
        Comp[1, 2] = setdiff(K[2], Sep[2])

        for i = 3 : s
            ipa = edgelist[i-1][1]
            Comp[i, 1:s] = Comp[ipa, 1:s]
            Comp[i, ipa] = setdiff(K[ipa], Sep[i])
            Comp[1, i] = setdiff(K[i], Sep[i]) 
            
            for j = reverse(2: i-1)
                Comp[j, i] = Comp[1, i]
                Sep[i] ⊊ Sep[j] && begin
                    # K_j and K_jpa belongs to one super clique in T^K_i
                    jpa = edgelist[j-1][1]
                    Comp[i, jpa] = union(Comp[i, jpa], Comp[i, j])
                    Comp[i, j] = Set()
                end
            end
            
            tag = []
            while ipa != 1 
                Sep[ipa] ⊊ Sep[i] && begin
                    # K_i and K_ipa belongs to one super clique in T^K_k
                    push!(tag, ipa)
                    for k in 1: ipa-1
                        Comp[k, ipa] =  Comp[k, i] = union(Comp[k, ipa], Comp[k, i])
                    end
                end
                ipa = edgelist[ipa-1][1]
            end
            
            !isempty(tag) && begin
                for k in 1: tag[1]-1
                    Comp[k, i] = Set()
                end
            end
        end
    end
    
    B = []
    for i in 1:s
        # Extract all non empty sets from the i-th row
        non_empty_elements = collect(filter(!isempty, Comp[i, :])) |> x -> [collect(s) for s in x]

        # Store non empty sets in B
        push!(B, non_empty_elements)
    end
    return B
end

"""
    icount(cc, memo, fmemo)
"""
function icount(cc, memo, fmemo, loop)
    G = cc[1] # graph
    mapping = cc[2] # mapping to original vertex numbers
    n = nv(G)
    
    # check memoization table
    mapG = Set(map(x -> mapping[x], vertices(G)))
    haskey(memo, mapG) && return memo[mapG]
    
    # do bfs over the clique tree 
    K, Sep, edgelist, s, cclique = cliquetree(G) 
    Comp = SCTrans(K, Sep, edgelist, s)
    sum = BigInt(0)
    Q = [1]
    vis = falses(s) 
    vis[1] = true
    pred = -1 * ones(Int, s) 
    while !isempty(Q)
        v = pop!(Q)
        for x in cclique[v] # [edge[2] for edge in edgelist if edge[1] == v]
            if !vis[x]
                push!(Q, x)
                vis[x] = true
                pred[x] = v
            end
        end

        prod = BigInt(1)
        for H in Comp[v]
            HH = induced_subgraph(G, H)
            prod *= icount((HH[1], map(x -> mapping[x], HH[2])), memo, fmemo, loop+1)
            #end
        end
        # compute correction term phi
        FP = []
        curr = v
        curr_succ = -1
        intersect_pred = -1
        while pred[curr] != -1
            curr = pred[curr]
            intersect_v = length(intersect(K[v], K[curr]))
            if curr_succ != -1
                intersect_pred = length(intersect(K[curr], K[curr_succ]))
            end
            curr_succ = curr
            if intersect_v == 0
                break
            end
            #if lastcut were strictly greater, v is not in bouquet
            # defined by cut between curr and curr_succ
            if intersect_v >= intersect_pred && (isempty(FP) || intersect_v < FP[end])
                push!(FP, intersect_v)
            end
        end
        push!(FP, 0)
        pmemo = zeros(BigInt, length(FP))
        sum += prod * phi(length(K[v]), 1, reverse(FP), fmemo, pmemo)
    end
    return memo[mapG] = sum
end

function MECsize(G)
    n = nv(G) 
    memo = Dict{Set, BigInt}() #mapping set of vertices -> AMO sum
    fmemo = zeros(BigInt, n)
    U = copy(G)
    U.ne = 0
    for i = 1:n
        filter!(j->has_edge(G, j, i), U.fadjlist[i])
        filter!(j->has_edge(G, i, j), U.badjlist[i])
        U.ne += length(U.fadjlist[i])
    end
    tres = 1
    for component in connected_components(U)
        cc = induced_subgraph(U, component)
        if !ischordal(cc[1])
            println("Undirected connected components are NOT chordal...Abort")
            println("Are you sure the graph is a CPDAG?")
            # is there anything more clever than just returning?
            return
        end
        tres *= icount(cc, memo, fmemo, 0)
    end

    return tres
end

n = 512
r = 0.34
i = 1
G = readgraph(string(, n, " ", r, " ", i, " uccg.in"), true)
MECsize(G)