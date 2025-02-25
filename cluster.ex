defmodule Cluster do
  def start do
    epoch_pid = spawn(__MODULE__, :rg, [%{}])

    send(epoch_pid, {:epoc})
  end

  # Replica group definition
  def rg(peers) do
    receive do
      {:epoc} ->

      # token -> {pid, version}
      updated_peers = Map.put(peers, 0, %{pid: self(), version: 1})
      IO.puts("updated_peers: #{inspect(updated_peers)}")

      rg(updated_peers)
    end

    rg(peers)
  end
end

# Start the cluster
Cluster.start()
