function compInit2WayGains(bins::Vector{Int}, fixed::Vector{Int}, H::Hypergraph, incidence::Incidence)
    e = H.e
    n = H.n
    netDegs = [zeros(Int, 2) for i in 1:e]
    gains = zeros(Int, n)
    initEdgeDegs!(H, bins, netDegs)
    initNodeGains!(H, fixed, bins, gains, netDegs, incidence)

    return (netDegs, gains)
end

function initEdgeDegs!(H::Hypergraph, bins::Vector{Int}, netDegs::Vector)
    partCost = 0
    edgeDegree = 0
    n = H.n
    e = H.e
    hedges = H.hedges
    eptr = H.eptr

    for i in 1:e
        u_loc = eptr[i]
        v_loc = eptr[i+1]
        for j in u_loc:v_loc-1
            v = hedges[j]
            netDegs[i][bins[v]+1] += 1
        end
    end
end

function initNodeGains!(H::Hypergraph, fixed::Vector{Int}, bins::Vector{Int}, gains::Vector{Int}, netDegs::Vector, incidence::Incidence)
    n_gain = 0
    eGain = 0
    pId = 0
    oId = 0
    fromDeg = 0
    toDeg = 0
    n = H.n
    i_hedges = incidence.hedges
    i_eptr = incidence.eptr
    h_hedges = H.hedges
    h_eptr = H.eptr

    if H.weighted == true
        w_ = H.w_
    else
        w_ = ones(Int, H.e)
    end

    for i in 1:n 
        if fixed[i] == 0
            pId = bins[i]
            oId = pId == 0 ? 1 : 0
            u_loc = i_eptr[i]
            v_loc = i_eptr[i+1]

            for j in u_loc:v_loc-1
                h = i_hedges[j]
                h_size = h_eptr[h+1]-h_eptr[h]
                eWt = w_[h]
                #=if h_size > _FM_max_fanout
                    continue
                end=#
                fromDeg = netDegs[h][pId+1]
                toDeg = netDegs[h][oId+1] 
                if toDeg == 0 && fromDeg > 0
                    eGain = -eWt
                elseif fromDeg == 1 && toDeg >= 0
                    eGain = eWt
                else
                    eGain = 0
                end
                n_gain += eGain
            end
            gains[i] = n_gain
            n_gain = 0
        end
    end
end

function updAfterMove!(gains::Vector{Int}, fixed::Vector{Int}, moved::Vector{Int}, marked::Vector{Int}, 
                       netDegs::Vector{Vector{Int}}, nIdx::Int, bins::Vector{Int}, H::Hypergraph, incidence::Incidence, order::Int, pass::Int)
    n = H.n
    e = H.e
    i_hedges = incidence.hedges
    i_eptr = incidence.eptr
    h_hedges = H.hedges
    h_eptr = H.eptr
    w_ = H.w_

    if H.weighted == false
        w_ = ones(Int, H.e)
    end

    moved[nIdx] = pass
    toPId = bins[nIdx]
    fromPId = toPId == 0 ? 1 : 0
    gains[nIdx] = -gains[nIdx]
    nbrs = Vector{Int}()

    for i in i_eptr[nIdx]:i_eptr[nIdx+1]-1
        h = i_hedges[i]
        eWt = w_[h]
        u_loc = h_eptr[h]
        v_loc = h_eptr[h+1]
        h_size = v_loc-u_loc
        netDegs[h][toPId+1] += 1
        netDegs[h][fromPId+1] -= 1

        for j in u_loc:v_loc-1
            v = h_hedges[j]
            if v == nIdx || fixed[v] > 0
                continue
            end
            nodePId = bins[v]
            fromDeg = netDegs[h][fromPId+1]
            toDeg = netDegs[h][toPId+1]

            if nodePId == fromPId
                if fromDeg == 1
                    gains[v] += eWt
                end
                if toDeg == 1
                    gains[v] += eWt
                end
            else
                if fromDeg == 0
                    gains[v] -= eWt
                end
                if toDeg == 2
                    gains[v] -= eWt
                end
            end

            if moved[v] != pass && marked[v] != order
                push!(nbrs, v)
                marked[v] = order
            end
        end
    end

    return nbrs
end

function updateGainHeap!(perm::Vector{Int}, bins::Vector{Int}, gainHeaps::Vector, gainHeapLocators::Vector, numNodes::Vector{Int}, gains::Vector{Int})
    nId = Int(0)
    pId = Int(0)
    heaploc = Int(0)
    
    for pIdx in 1:length(perm)
        nId = perm[pIdx]
        pId = bins[nId]
        push!(gainHeaps[pId+1], [nId, gains[nId]])
        numNodes[pId+1] += 1
        heaploc = numNodes[pId+1]
        gainHeapLocators[nId] = [pId+1, numNodes[pId+1]]
        heapifyUp!(heaploc, gainHeapLocators, gainHeaps, gains[nId], pId+1)
    end
end

function rollBack!(minCostOrder::Int, fixed::Vector{Int}, binsArea::Array{Int}, gains::Vector{Int}, swaps::Vector{Int}, bins::Vector{Int}, area::Array{Int}, 
                   moved::Vector{Int}, marked::Vector{Int}, netDegs::Vector, H::Hypergraph, incidence::Incidence, pass::Int, order::Int, cut_size::Int)
    node = 0
    fromId = 0
    toId = 0
    nbrs = Vector{Int}()

    @inbounds for oIdx in minCostOrder+1:length(swaps)
        node = swaps[oIdx]
        fromId = bins[node] 
        toId = fromId == 0 ? 1 : 0
        binsArea[:, fromId+1] -= area[node, :]
        binsArea[:, toId+1] +=  area[node, :]
        bins[node] = toId
        cut_size += gains[node]
        nbrs = updAfterMove!(gains, fixed, moved, marked, netDegs, node, bins, H, incidence, order, pass) 
    end
end

function updateNbrs!(nbrs::Vector{Int}, gains::Vector{Int}, gainHeapLocators::Vector, gainHeaps::Vector, numNodes::Vector{Int}, bins::Vector{Int})
    for nbrIdx in 1:length(nbrs)
        nbr = nbrs[nbrIdx]
        newGain = gains[nbr]
        locT = gainHeapLocators[nbr]
        oldGain = gainHeaps[locT[1]][locT[2]][2] 
        heapify!(nbr, numNodes, newGain, oldGain, bins, gainHeapLocators, gainHeaps)
    end
end

function heapify!(node::Int, numNodes::Vector{Int}, newGain::Int, oldGain::Int, bins::Vector{Int}, gainHeapLocators::Vector, gainHeaps::Vector)
    partId = bins[node]+1
    heapLoc = gainHeapLocators[node][2]
    gainHeaps[partId][heapLoc][2] = newGain

    if oldGain > newGain
        heapifyDown!(heapLoc, numNodes[partId], gainHeapLocators, gainHeaps, newGain, partId)
    elseif oldGain < newGain
        heapifyUp!(heapLoc, gainHeapLocators, gainHeaps, newGain, partId)
    end
end

function heapifyUp!(heapLoc::Int, gainHeapLocators::Vector, gainHeaps::Vector, newGain::Int, partId::Int)
    parent = 0
    gainHeap = Vector()
    h_node = 0
    child = zeros(Int, 2)

    while heapLoc > 1
        parent = heapLoc >> 1
        if newGain > gainHeaps[partId][parent][2]
            child = gainHeaps[partId][heapLoc]
            gainHeaps[partId][heapLoc] = gainHeaps[partId][parent]
            h_node = gainHeaps[partId][parent][1]
            gainHeapLocators[h_node] = [partId, heapLoc]
            gainHeaps[partId][parent] = child
            gainHeapLocators[child[1]] = [partId, parent]
            heapLoc = parent
        else
            break
        end
    end
end

function heapifyDown!(heaploc::Int, numNodes::Int, gainHeapLocators::Vector, gainHeaps::Vector, newGain::Int, partId::Int)
    j = heaploc << 1
    gain_l = Vector()
    gain_r = Vector()
    parent = zeros(Int ,2)
    child = zeros(Int, 2)

    while j <= numNodes
        gain_l = gainHeaps[partId][j]

        if j+1 <= numNodes
            gain_r = gainHeaps[partId][j+1]
            if gain_l[2] < gain_r[2]
                j += 1
            end
        else
            if newGain > gain_l[2]
                break
            end
        end
        
        if newGain > gain_l[2] && newGain > gain_r[2]
            break
        end

        parent = gainHeaps[partId][heaploc]
        child = gainHeaps[partId][j]
        gainHeaps[partId][heaploc] = child
        gainHeapLocators[child[1]] = [partId, heaploc]
        gainHeaps[partId][j] = parent
        gainHeapLocators[parent[1]] = [partId, j]
        heaploc = j
        j = heaploc << 1
    end
end

function bestNodeToMove(gainHeaps::Vector, gainHeapLocators::Vector, binsArea::Array{Int}, area::Array{Int}, numNodes::Vector{Int}, target_area::Array{Int})  
    ptr = 1
    best_node = 0
    best_side = 0

    if numNodes[1] == 0 && numNodes[2] == 0
        return (-1, -1)

    elseif numNodes[1] == 0 && numNodes[2] > 0
        node = gainHeaps[2][ptr][1]
        done = binsArea[:, 1] .+ area[node] <= target_area[:, 1]

        while done == false
            if ptr < numNodes[2]
                ptr += 1
                done = binsArea[:, 1] .+ area[node] <= target_area[:, 1]
            else
                return (-1, -1)
            end
        end

        best_node = gainHeaps[2][ptr][1]
        best_side = 1

    elseif numNodes[2] == 0 && numNodes[1] > 0
        node = gainHeaps[1][ptr][1]
        done = binsArea[:, 2] .+ area[node] <= target_area[:, 2]

        while done == false
            if ptr < numNodes[1]
                ptr += 1
                done = binsArea[:, 2] .+ area[node] <= target_area[:, 2]
            else
                return (-1, -1)
            end
        end

        best_node = gainHeaps[1][ptr][1]
        best_side = 0

    else
        gain_0 = gainHeaps[1][1][2]
        gain_1 = gainHeaps[2][1][2]

        if gain_0 == gain_1 
            node_0 = gainHeaps[1][ptr][1]
            node_1 = gainHeaps[2][ptr][1]
            balance_0 = binsArea[:, 2] .+ area[node_0] <= target_area[:, 2]
            balance_1 = binsArea[:, 1] .+ area[node_1] <= target_area[:, 1]
        
            if balance_0 == true && balance_1 == true
                best_node = node_0 < node_1 ? node_0 : node_1
                best_side = noed_0 < noed_1 ? 0 : 1
            elseif balance_0 == true && balance_1 == false
                best_node = node_0
                best_side = 0
            elseif balance_0 == false && balance_1 == true
                best_node = node_1
                best_side = 1
            else
                return (-1, -1) #need to rework this
            end

        else
            side = gainHeaps[1][1][2] > gainHeaps[2][1][2] ? 0 : 1
            other_side = side == 0 ? 1 : 0
            node = gainHeaps[side+1][ptr][1]
            balance = binsArea[:, other_side+1] .+ area[node] <= target_area[:, other_side+1]

            if balance == false
                if ptr == numNodes[side+1]
                    heap_block = gainHeaps[other_side+1]
                    node = heap_block[ptr][1] 
                    balance = binsArea[:, other_side+1] .+ area[node] <= target_area[:, other_side+1]

                    while balance == false
                        if ptr < numNodes[other_side+1]
                            ptr += 1
                            node = heap_block[ptr][1]
                            balance = binsArea[:, other_side+1] .+ area[node] <= target_area[:, other_side+1]
                        else
                            return (-1, -1)
                        end
                    end

                    best_side = other_side
                    best_node = node
                else
                    best_side = other_side
                    heap_block = gainHeaps[other_side+1]
                    best_node = heap_block[ptr][1]
                end
            else
                best_side = side
                heap_block = gainHeaps[side+1]
                best_node = heap_block[ptr][1]
            end
        end
    end

    gain_block = gainHeaps[best_side+1][numNodes[best_side+1]]
    gainHeaps[best_side+1][ptr] = gain_block
    gainHeapLocators[gain_block[1]] = [best_side+1, ptr]
    heapifyDown!(ptr, numNodes[best_side+1]-1, gainHeapLocators, gainHeaps, gain_block[2], best_side+1)
    numNodes[best_side+1] -= 1

    return (best_node, best_side)
end

function pop_heap!(side::Int, gainHeaps::Vector, gainHeapLocators::Vector, numNodes::Vector{Int})
    success_flag = false

    if numNodes[side] > 1
        gain_block = gainHeaps[side][numNodes[side]]
        gainHeaps[side][1] = gain_block
        gainHeapLocators[gain_block[1]] = [side, 1]
        heapifyDown!(1, numNodes[side]-1, gainHeapLocators, gainHeaps, gain_block[2], side)
        numNodes[side] -= 1
        success_flag = true
    elseif numNodes[side] == 1
        numNodes[side] = 0
        success_flag = true
    else 
        success_flag = false
    end

    return success_flag
end

function improveAreaCost(bins::Vector{Int}, binsArea::Array{Int}, fixed::Vector{Int}, area::Array{Int}, H::Hypergraph, 
                        B::Incidence, cut_size::Int, target_cut::Int, max_cut::Int, target_area::Array{Int}, capacity::Array{Int}, cut_cost::Float64)
    init_cost = deepcopy(cut_cost)
    n = H.n
    side = 0
    base_cut = 1e06
    base_area = 1e08
    done = false
    order = 1
    pass = 1
    keep_going = 0
    moved = zeros(Int, n)
    marked = zeros(Int, n)
    (netDegs, gains) = compInit2WayGains(bins, fixed, H, B)
    perm = sortperm(gains, rev=true)
    gainHeaps = [Vector(), Vector()]
    gainHeapLocators = [zeros(Int, 2) for i in 1:n]
    numNodes = [0, 0]
    updateGainHeap!(perm, bins, gainHeaps, gainHeapLocators, numNodes, gains)

    if binsArea[:, 1] <= target_area[:, 1] && binsArea[:, 2] <= target_area[:, 2]
        side =  binsArea[:, 1] > binsArea[:, 2] ? 0 : 1
    elseif binsArea[:, 1] > target_area[:, 1]
        side = 0
    elseif binsArea[:, 2] > target_area[:, 2]
        side = 1
    end

    while done == false
        block = gainHeaps[side+1][1]
        nId = block[1]
        pop_flag = pop_heap!(side+1, gainHeaps, gainHeapLocators, numNodes)    

        if pop_flag == false
            done = true
            continue
        end

        moved[nId] = pass

        if fixed[nId] > 0
            continue
        end

        best_node = nId
        fromP = side
        toP = side == 0 ? 1 : 0
        cut_size -= gains[best_node]
        excess_cut = cut_size - target_cut
        exp_cut = excess_cut/(max_cut-target_cut)
        cut_cost = base_cut^exp_cut
        excess_area_0 = binsArea[1, 1] - target_area[1, 1] 
        excess_area_1 = binsArea[1, 2] - target_area[1, 2]
        exp_area_0 = excess_area_0/(capacity[1, 1]-target_area[1, 1])
        exp_area_1 = excess_area_1/(capacity[1, 2]-target_area[1, 2])
        area_cost = base_area^exp_area_0 + base_area^exp_area_1
        total_cost = area_cost + cut_cost

        if binsArea[1, fromP] > target_area[1, fromP] || total_cost < init_cost
            keep_going = 0
            best_node = nId
            bins[best_node] = toP
            binsArea[:, fromP+1] -= area[best_node, :]
            binsArea[:, toP+1] += area[best_node, :]
            nbrs = updAfterMove!(gains, fixed, moved, marked, netDegs, nId, bins, H, B, order, pass)
            updateNbrs!(nbrs, gains, gainHeapLocators, gainHeaps, numNodes, bins)
            order += 1
            init_cost = total_cost
        else
            keep_going += 1

            if keep_going == 2
                cut_size += gains[best_node]
                done = true
                continue
            else
                best_node = nId
                bins[best_node] = toP
                binsArea[:, fromP+1] -= area[best_node, :]
                binsArea[:, toP+1] += area[best_node, :]
                nbrs = updAfterMove!(gains, fixed, moved, marked, netDegs, best_node, bins, H, B, order, pass)
                updateNbrs!(nbrs, gains, gainHeapLocators, gainHeaps, numNodes, bins)
                order += 1
                init_cost = total_cost
            end
        end
    end

    return (cut_size, bins, binsArea)
end

function improveCutCost(bins::Vector{Int}, binsArea::Array{Int}, fixed::Vector{Int}, area::Array{Int}, H::Hypergraph, 
                        B::Incidence, cut_size::Int, target_cut::Int, max_cut::Int, target_area::Array{Int}, capacity::Array{Int}, cut_cost::Float64, early_exit::Bool)
    init_cost = deepcopy(cut_size)
    prev_cost = init_cost
    min_cost = init_cost
    max_passes = 10
    n = H.n
    side = 0    
    base_cut = 1e06
    base_area = 1e08
    done = false
    order = 1
    order_loc = 0
    pass = 1
    keep_going = 0
    keep_going_threshold = 10
    saturation = 0
    saturation_threshold = 3
    chain_count = 0
    moved = zeros(Int, n)
    marked = zeros(Int, n)
    (netDegs, gains) = compInit2WayGains(bins, fixed, H, B)
    perm = sortperm(gains, rev=true)
    gainHeaps = [Vector(), Vector()]
    gainHeapLocators = [zeros(Int, 2) for i in 1:n]
    numNodes = [0, 0]
    updateGainHeap!(perm, bins, gainHeaps, gainHeapLocators, numNodes, gains)

    if n <= 20_000
        chain_count = n
    else
        chain_count = 10_000
    end

    if early_exit == true
        chain_count = 200
        keep_going_threshold = 5
        saturation_threshold = 2
    end

    while done == false
        swaps = Vector{Int}()
        perm = sortperm(gains, rev=true)
        gainHeaps = [Vector(), Vector()]
        gainHeapLocators = [zeros(Int, 2) for i in 1:n]
        numNodes = [0, 0]
        updateGainHeap!(perm, bins, gainHeaps, gainHeapLocators, numNodes, gains)

        for i in 1:chain_count   
            if keep_going == keep_going_threshold
                break
            end
            
            (best_node, best_side) = bestNodeToMove(gainHeaps, gainHeapLocators, binsArea, area, numNodes, target_area)

            if best_node == -1 
                break
            end

            if fixed[best_node] > 0
                continue
            end

            push!(swaps, best_node)
            from = best_side
            to = from == 0 ? 1 : 0
            binsArea[:, from+1] -= area[best_node, :]
            binsArea[:, to+1] += area[best_node, :]
            bins[best_node] = to
            cut_size -= gains[best_node]
            nbrs = updAfterMove!(gains, fixed, moved, marked, netDegs, best_node, bins, H, B, order, pass)
            updateNbrs!(nbrs, gains, gainHeapLocators, gainHeaps, numNodes, bins)
            order += 1
            
            #=
            excess_cut = cut_size - target_cut
            exp_cut = excess_cut/(max_cut-target_cut)
            cut_cost = base_cut^exp_cut
            excess_area_0 = binsArea[1, 1] - target_area[1, 1] 
            excess_area_1 = binsArea[1, 2] - target_area[1, 2]
            exp_area_0 = excess_area_0/(capacity[1, 1]-target_area[1, 1])
            exp_area_1 = excess_area_1/(capacity[1, 2]-target_area[1, 2])
            area_cost = base_area^exp_area_0 + base_area^exp_area_1
            total_cost = area_cost + cut_cost
            =#
            total_cost = cut_size

            if total_cost < min_cost
                min_cost = total_cost
                order_loc = order
                keep_going = 0
            else 
                if total_cost > prev_cost
                    keep_going += 1
                else
                    keep_going = 0
                end
            end

            prev_cost = total_cost
        end

        if min_cost >= init_cost
            saturation += 1
        else
            saturation = 0
        end

        if length(swaps) > 0
            init_cost = min_cost
            rollBack!(order_loc, fixed, binsArea, gains, swaps, bins, area, moved, marked, netDegs, H, B, pass, order, cut_size)  
        end

        pass += 1

        if pass <= max_passes
            done = true
        end

        if saturation <= saturation_threshold
            done = true
        end
    end

    return (cut_size, bins, binsArea)
end