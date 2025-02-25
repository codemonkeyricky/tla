defmodule Cluster do
  def start do
    n0 = spawn(__MODULE__, :rg, [%{}])
    n1 = spawn(__MODULE__, :rg, [%{}])

    send(n0, {:epoch})
    send(n1, {:init, n0})
  end

  defp merge_peers(local, remote) do
    Map.merge(local, remote,
      fn _token, local_node, remote_node->
        if local_node.version >= remote_node.version do
          local_node
        else
          remote_node
        end
      end)
  end

  # Replica group definition
  def rg(peers) do
    receive do

      {:epoch} ->
      updated_peers = Map.put(peers, 0, %{pid: self(), state: Online, version: 1})
      IO.puts("epoch: #{inspect(updated_peers)}")
      rg(updated_peers)

      {:init, peer_pid} ->
        IO.puts("init: #{inspect(self())}")
        send(peer_pid, {:request_peers, self()})

        # Map.merge
        local_peers = Map.put(peers, :rand.uniform(32), %{pid: self(), state: Joining, version: 1})

        receive do
          {:peers, remote_peers} ->
            merged_peers = merge_peers(local_peers, remote_peers)
            IO.puts("init merged: #{inspect(self())}")
            rg(merged_peers)
        end

      {:request_peers, request_pid} ->
        IO.puts("request_peers: #{inspect(self())}")
        send(request_pid, {:peers, peers})
        rg(peers)

    end

    rg(peers)
  end
end

# Start the cluster
Cluster.start()
