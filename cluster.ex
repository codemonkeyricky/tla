defmodule Cluster do
  def start do
    epoch_pid = spawn(__MODULE__, :rg, [0, 1, %{}])

    send(epoch_pid, {:epoc})
  end

  # Replica group definition
  def rg(token, version, peers) do
    receive do
      {:epoc} ->

      updated_peers = Map.put(peers, token, %{version: version, pid: self()})
      IO.puts("updated_peers: #{inspect(updated_peers)}")

      rg(token, version, updated_peers)
    end

    rg(token, version, peers)
  end
end

# Start the cluster
Cluster.start()
