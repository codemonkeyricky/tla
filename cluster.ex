defmodule Cluster do
  def start do
    n0 = spawn(__MODULE__, :rg, [%{name: "n0"}, %{}])
    n1 = spawn(__MODULE__, :rg, [%{name: "n1"}, %{}])
    # n2 = spawn(__MODULE__, :rg, [%{name: "n2"}, %{}])

    send(n0, {:epoch})
    send(n1, {:join, n0})
    # send(n2, {:join, n1})
  end

  defp merge_ring(local, remote) do
    Map.merge(local, remote, fn _pid, local_node, remote_node ->
      if local_node.version >= remote_node.version do
        local_node
      else
        remote_node
      end
    end)
  end

  # defp handle_join() do
  #   keys = local_ring |> Map.keys() |> Enum.sort()
  #   key_index = Enum.find_index(keys, fn k -> k == property.token end)
  # end

  # defmodule Property do
  #   defstruct name: nil, age: nil, email: nil
  # end

  # Replica group definition
  def rg(property, local_ring) do
    receive do
      {:epoch} ->
        # IO.puts("epoch: #{inspect(property.name)}")
        # name = property.name
        Process.register(self(), String.to_existing_atom(property.name))
        # raise "xxx"
        updated_property = Map.put(property, :token, 0)
        updated_local_ring = Map.put(local_ring, self(), %{token: 0, state: Online, version: 1})
        IO.puts("epoch: #{inspect(updated_property)}")
        rg(updated_property, updated_local_ring)

      {:join, peer_pid} ->
        IO.puts("join: #{inspect(self())}")
        Process.register(self(), String.to_existing_atom(property.name))
        token = :rand.uniform(32)
        updated_property = Map.put(property, :token, 0)
        updated_property = %{token: token}
        local_ring = Map.put(local_ring, self(), %{token: token, state: Joining, version: 1})
        send(peer_pid, {:gossip_req, self(), local_ring})
        rg(updated_property, local_ring)

      {:gossip_ack, remote_ring} ->
        # IO.puts("#{inspect(self())}: gossip_ack")
        merged_local_ring = merge_ring(local_ring, remote_ring)
        send(self(), {:heartbeat})
        IO.puts("#{inspect(self())}: gossip_ack: merged #{inspect(merged_local_ring)}")
        rg(property, merged_local_ring)

      {:gossip_req, remote_pid, remote_ring} ->
        merged_local_ring = merge_ring(local_ring, remote_ring)
        send(remote_pid, {:gossip_ack, merged_local_ring})
        send(self(), {:heartbeat})
        IO.puts("#{inspect(self())}: gossip_req: merged #{inspect(merged_local_ring)}")
        rg(property, merged_local_ring)

      {:stats} ->
        IO.puts("#{inspect(self())}: stats: #{inspect(property)}")
        IO.puts("#{inspect(self())}: stats: #{inspect(local_ring)}")

      {:heartbeat} ->
        # IO.puts("#{inspect(self())}: heartbeat")
        keys = local_ring |> Map.values() |> Enum.map(& &1.token)

        if length(keys) == 1 do
          raise "invalid ring scan with a single node"
        end

        # find previous token
        key_index = Enum.find_index(keys, fn k -> k == property.token end)

        prev_token =
          case key_index do
            0 -> List.last(keys)
            _ -> Enum.at(keys, key_index - 1)
          end

        # Look for all pids with this token
        matching_pids =
          local_ring
          |> Enum.filter(fn {_pid, node} -> node.token == prev_token end)
          |> Enum.map(fn {pid, _node} -> pid end)

        # Set of ptoken nodes that want to join
        joining_set =
          local_ring
          |> Enum.filter(fn {pid, _node} -> MapSet.member?(MapSet.new(matching_pids), pid) end)
          |> MapSet.new()

        # Number of online nodes with ptoken
        online_count =
          Enum.reduce(matching_pids, 0, fn pid, acc ->
            if local_ring[pid].state == :Online do
              acc + 1
            else
              acc
            end
          end)

        case online_count do
          # No online node claimed this token, pick a node to online
          0 ->
            IO.puts("#{inspect(self())}: ### #{inspect(joining_set)}")

            to_online = List.first(MapSet.to_list(joining_set))
            prev_value = local_ring[to_online]

            updated_ring =
              Map.put(local_ring, to_online, %{
                token: prev_value.pid,
                state: Online,
                version: prev_value.version + 1
              })

            send(to_online, {:gossip_req, self(), updated_ring})
            rg(property, updated_ring)

          1 ->
            # Another node is already online with this token
            # Reject one join request

            to_retry = List.first(MapSet.to_list(joining_set))
            send(to_retry, {:try_new_token})
            rg(property, local_ring)

          _ ->
            # error
            raise "multiple online nodes with same token!"
        end
    end

    rg(property, local_ring)
  end
end

# Start the cluster
Cluster.start()
