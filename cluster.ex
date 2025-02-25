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
        local_peers = Map.put(peers, :rand.uniform(32), %{pid: self(), state: Joining, version: 1})
        send(peer_pid, {:gossip_req, self(), local_peers})

      {:gossip_ack, remote_peers} ->
        IO.puts("#{inspect(self())}: gossip_ack")
        merged_peers = merge_peers(peers, remote_peers)
        send(self(), {:heartbeat})
        rg(merged_peers)

      {:gossip_req, remote_pid, remote_peers} ->
        IO.puts("#{inspect(self())}: gossip_req")
        merged_peers = merge_peers(peers, remote_peers)
        send(remote_pid, {:gossip_ack, merged_peers})
        send(self(), {:heartbeat})
        rg(merged_peers)

      {:heartbeat} ->
        IO.puts("#{inspect(self())}: heartbeat")

    end

    rg(peers)
  end
end

# Start the cluster
Cluster.start()
