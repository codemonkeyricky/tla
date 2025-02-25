defmodule Cluster do
  def start do
    n0 = spawn(__MODULE__, :rg, [%{}])
    n1 = spawn(__MODULE__, :rg, [%{}])

    send(n0, {:epoch})
    send(n1, {:init, n0})
  end

  defp merge_ring(local, remote) do
    Map.merge(local, remote,
      fn _token, local_node, remote_node->
        if local_node.version >= remote_node.version do
          local_node
        else
          remote_node
        end
      end)
  end

  # defmodule Property do
  #   defstruct name: nil, age: nil, email: nil
  # end

  # Replica group definition
  def rg(ring) do
    receive do

      {:epoch} ->
        updated_ring = Map.put(ring, 0, %{pid: self(), state: Online, version: 1})
        IO.puts("epoch: #{inspect(updated_ring)}")
        rg(updated_ring)

      {:init, peer_pid} ->
        IO.puts("init: #{inspect(self())}")
        local_ring = Map.put(ring, :rand.uniform(32), %{pid: self(), state: Joining, version: 1})
        send(peer_pid, {:gossip_req, self(), local_ring})

      {:gossip_ack, remote_ring} ->
        IO.puts("#{inspect(self())}: gossip_ack")
        merged_ring = merge_ring(ring, remote_ring)
        send(self(), {:heartbeat})
        rg(merged_ring)

      {:gossip_req, remote_pid, remote_ring} ->
        IO.puts("#{inspect(self())}: gossip_req")
        merged_ring = merge_ring(ring, remote_ring)
        send(remote_pid, {:gossip_ack, merged_ring})
        send(self(), {:heartbeat})
        rg(merged_ring)

      {:heartbeat} ->
        IO.puts("#{inspect(self())}: heartbeat")
        keys = ring |> Map.keys() |> Enum.sort()
        IO.puts("#{inspect(self())}: heartbeat: #{inspect(keys)}")
        # my_token = ring.
        # key_index = Enum.find_index(keys, fn k -> k == key end)

        # case k do
        #   end



    end

    rg(ring)
  end
end

# Start the cluster
Cluster.start()
