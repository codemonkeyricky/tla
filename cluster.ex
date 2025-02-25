defmodule Cluster do
  def start do
    n0 = spawn(__MODULE__, :rg, [%{}, %{}])
    n1 = spawn(__MODULE__, :rg, [%{}, %{}])

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
  def rg(property, local_ring) do
    receive do

      {:epoch} ->
        updated_property = %{token: 0}
        updated_local_ring = Map.put(local_ring, 0, %{pid: self(), state: Online, version: 1})
        IO.puts("epoch: #{inspect(updated_local_ring)}")
        rg(updated_property, updated_local_ring)

      {:init, peer_pid} ->
        IO.puts("init: #{inspect(self())}")
        token = :rand.uniform(32)
        updated_property = %{token: token}
        local_ring = Map.put(local_ring, token , %{pid: self(), state: Joining, version: 1})
        send(peer_pid, {:gossip_req, self(), local_ring})
        rg(updated_property, local_ring)

      {:gossip_ack, remote_ring} ->
        IO.puts("#{inspect(self())}: gossip_ack")
        merged_local_ring = merge_ring(local_ring, remote_ring)
        send(self(), {:heartbeat})
        rg(property, merged_local_ring)

      {:gossip_req, remote_pid, remote_ring} ->
        IO.puts("#{inspect(self())}: gossip_req")
        merged_local_ring = merge_ring(local_ring, remote_ring)
        send(remote_pid, {:gossip_ack, merged_local_ring})
        send(self(), {:heartbeat})
        rg(property, merged_local_ring)

      {:heartbeat} ->
        # IO.puts("#{inspect(self())}: heartbeat")
        keys = local_ring |> Map.keys() |> Enum.sort()
        IO.puts("#{inspect(self())}: heartbeat: #{inspect(keys)}")
        # my_token = local_ring.
        key_index = Enum.find_index(keys, fn k -> k == property.token end)
        IO.puts("#{inspect(self())}: heartbeat: token #{inspect(property.token)}")
        # IO.puts("#{inspect(self())}: heartbeat: key_index #{inspect(key_index)}")
        # IO.puts("#{inspect(self())}: heartbeat: token index #{inspect(key_index)}")
        prev_token =
          case key_index do
            0 -> prev_token = List.last(keys)
            _ -> prev_token = Enum.at(keys, key_index - 1)
          end
        IO.puts("#{inspect(self())}: heartbeat: prev_token #{inspect(prev_token)}")

        # case k do
        #   end
    end

    rg(property, local_ring)
  end
end

# Start the cluster
Cluster.start()
