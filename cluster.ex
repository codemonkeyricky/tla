defmodule ProcessExample do
  def run_processes(count) do
    # Spawn `count` number of processes
    Enum.each(1..count, fn _ ->
      spawn(fn -> process_work(0) end)
    end)
  end

  defp process_work(k) do
    # Simulate some work
    # Sleep for 1 second
    # :timer.sleep(1000)
    if rem(k, 100) == 0 do
      IO.puts("Process #{inspect(self())} finished work")
    end

    process_work(k + 1)
  end
end

# Run 2,000 processes
ProcessExample.run_processes(1_000_000)
